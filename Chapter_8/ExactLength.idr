-- import Data.Vect

data Vect : Nat -> Type -> Type where
     Nil  : Vect Z a
     (::) : a -> Vect k a -> Vect (S k) a

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
    Same : (num : Nat) -> EqNat num num

-- sameS : (k : Nat) -> (j : Nat) -> (eq : EqNat k j) -> EqNat (S k) (S j)
-- sameS k k (Same k) = Same (S k)


checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEqNat Z Z = Just Refl
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
    Nothing => Nothing
    Just prf => Just (cong prf)
-- checkEqNat (S k) (S j) = case checkEqNat k j of
--     Nothing => Nothing
--     Just (Same j) => Just (Same (S j))


myExactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
myExactLength {m} len input = case checkEqNat m len of
    Nothing => Nothing
    Just Refl => Just input



total same_cons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
same_cons prf = cong prf

total same_lists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists prf_x prf_xs = case prf_x of
    Refl => same_cons prf_xs


-- reverseProof : Vect (k + 1) elem -> Vect (S k) elem
-- reverseProof {k} result = rewrite plusCommutative 1 k in result
--
-- myReverse : Vect n elem -> Vect n elem
-- myReverse [] = []
-- myReverse {n = S k} (x :: xs) = reverseProof (myReverse xs ++ [x])

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = sym (plusZeroRightNeutral m)
myPlusCommutes (S k) m = rewrite myPlusCommutes k m in plusSuccRightSucc m k

rev_proof_nil : Vect n a -> Vect (n + 0) a
rev_proof_nil {n} xs = rewrite plusZeroRightNeutral n in xs

rev_proof_xs : Vect ((S n) + len) a -> Vect (plus n (S len)) a
rev_proof_xs {n} {len} xs = rewrite sym (plusSuccRightSucc n len) in xs

myReverse : Vect n a -> Vect n a
myReverse xs = reverse' [] xs
    where reverse' : Vect n a -> Vect m a -> Vect (n+m) a
          reverse' acc [] = rev_proof_nil acc
          reverse' acc (x :: xs) = rev_proof_xs (reverse' (x :: acc) xs)

headUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (x = y) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect n a} -> {ys : Vect n a} -> (contra : (xs = ys) -> Void) -> ((x :: xs) = (y :: ys)) -> Void
tailUnequal contra Refl = contra Refl

total same_cons_vect : {xs : Vect n a} -> {ys : Vect n a} -> xs = ys -> x :: xs = x :: ys
same_cons_vect prf = cong prf

total same_vect : {xs : Vect n a} -> {ys : Vect n a} -> x = y -> xs = ys -> x :: xs = y :: ys
same_vect prf_x prf_xs = case prf_x of
    Refl => same_cons_vect prf_xs

DecEq a => DecEq (Vect n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) =
      case decEq x y of
          Yes x_prf => case decEq xs ys of
              Yes xs_prf => Yes $ same_vect x_prf xs_prf
              No xs_contra => No (tailUnequal xs_contra)
          No x_contra => No $ headUnequal x_contra
