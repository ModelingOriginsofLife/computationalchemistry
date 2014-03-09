module LambTypable

where

import LambRandGen(Term(..))

data Type = Var Int
          | Arrow Type Type
          deriving Show

buildConstraint :: Term -> (Type, [(Type,Type)])
buildConstraint t =
    let (ty,[],constraint,_) = build t 0 0
    in (ty, constraint)
    where
        build :: Term -> Int -> Int -> (Type, [Type], [(Type,Type)], Int)
        build (Index i) d cu = 
          let ii = fromIntegral i
          in (Var (cu+ii-1), [Var j | j<-[cu..cu+d-1]],[],cu+d)
        build (Abs t) d cu =
          let (ty,(a:cntxt),constraint,cu') = build t (d+1) cu
          in ((Arrow a ty),cntxt,constraint,cu')
        build (App t1 t2) d cu =
          let (ty1, cntxt1, constraint1, cu1) = build t1 d cu in
          let (ty2, cntxt2, constraint2, cu2) = build t2 d cu1 in
          let ty = (Var cu2) in (ty,
                                 cntxt1,
                                 (ty1,(Arrow ty2 ty)):(zip cntxt1 cntxt2)
                                    ++ constraint1 ++ constraint2,
                                    cu2+1)

decompose :: (Type,Type) -> [(Type,Type)] 
decompose ((Arrow ty1 ty2), (Arrow ty1' ty2')) = 
  decompose (ty1,ty1') ++ decompose (ty2,ty2') 
decompose ((Arrow ty1 ty2),(Var i)) = [(Var i,(Arrow ty1 ty2))] 
decompose (ty1,ty2) = [(ty1,ty2)]

nonTrivialEq :: (Type,Type) -> Bool 
nonTrivialEq (Var i, Var j) = i /= j 
nonTrivialEq (ty1, ty2) = True

occursInType :: Type -> Type -> Bool
occursInType (Var i) (Var j) = False 
occursInType (Var i) (Arrow ty1 ty2) = inType (Var i) ty1 || 
                                         inType (Var i) ty2
    where inType :: Type -> Type -> Bool
          inType (Var i) (Var j) = i == j 
          inType (Var i) (Arrow ty1 ty2) = inType (Var i) ty1 || 
                                            inType (Var i) ty2

replaceInType :: (Type,Type) -> Type -> Type 
replaceInType (Var i, ty) (Var j) = if i == j then ty else (Var j)
replaceInType (Var i, ty) (Arrow ty1 ty2) = 
  Arrow (replaceInType (Var i, ty) ty1)
        (replaceInType (Var i, ty) ty2)

replaceInEq :: (Type,Type) -> (Type,Type) -> (Type,Type) 
replaceInEq (Var i,ty) (ty1,ty2) = 
  (replaceInType (Var i,ty) ty1, replaceInType (Var i,ty) ty2)
nio
solve :: [(Type,Type)] -> [(Type,Type)] -> ([(Type,Type)],[(Type,Type)],Bool)
solve ((Var i,ty):l) sol = if occursInType (Var i) ty
    then ((Var i,ty):l,sol,False) -- cycle detected 
    else solve (map (replaceInEq (Var i,ty)) l) 
                                         ((Var i,ty):sol)
solve (eq:l) sol = 
  solve (filter nonTrivialEq (decompose eq) ++ l) sol 
solve [] sol = ([],sol,True)

--e.g.isTypable (LambRandGen.unrankNF 3 0 5) = True
--    LambRandGen.unrankNF 3 0 5 = Abs (Abs (App (Index 1) (Index 2)))
--    \x.\y.y x
--e.g.isTypable (Abs (App (Index 1) (Index 1))) = False
--    LambRandGen.unrankT 1 1 3 = App (Index 1) (Index 1)
--    \x. x x 
isTypable :: Term -> Bool 
isTypable t = let (_,c) = buildConstraint t 
               in let (_,_,b) = solve c [] in b
