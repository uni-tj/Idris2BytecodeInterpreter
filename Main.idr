module Main 
-- idris2 main.idr rlwrap idris2
import Data.Vect
import Decidable.Equality

{- removeElem:DecEq a => (value:a)-> (xs:Vect (S n) a )-> Vect n a
removeElem value (x :: xs) = case decEq value x of 
                                  Yes prf => xs
                                  No contra => x :: removeElem val xs -}

-- This errors because the Value might not be  in the Vec5t

{- removeElem:DecEq a => (value:a)-> (xs:Vect (S n) a )-> Vect n a
removeElem value (x :: xs) = case decEq value x of 
                                  Yes prf => xs
                                  No contra => x :: removeElem val xs -}

-- We want a Type like Eq Nat which behaves like this:
-- Elem: (value:a)-> (xs:Vect k a)-> Type
{- oneInVector : Elem 1 [1,2,3]
maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]

fourNotInVector : Elem 4 [1,2,3] -> Void
peteNotInVector : Elem "Pete" ["John", "Paul", "George", "Ringo"] -> Void -}


-- We define a new Typw like EqNat:
data Elem : a -> Vect k a -> Type where 
   Here : Elem x (x::xs)-- Tells us that x is the First Element of the Vector 
   There: (later : Elem x xs) -> Elem x (y::xs)-- Tells us that if x is in the Vector xs x is also in (y::xs)

oneInVector : Elem 1 [1,2,3]
oneInVector = ?gere 

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector =  ?maryInVector_rhs_0


-- removeElem:(value:a) -> (xs:Vect (S n) a) -> (prf: Elem value xs) -> Vect n a
-- removeElem value (value :: xs) Here = xs
-- removeElem value (y :: xs) (There later) = ?removeElem_rhs_1

 -- Inspect Hole. What is the difference 

-- DOESNT WORK LIKE IN THE BOOK N Needs to be implicit in the type

-- removeElem:{n:_}->(value:a) -> (xs:Vect (S n) a) -> (prf: Elem value xs) -> Vect n a
-- removeElem value (value :: xs) Here = xs
-- removeElem {n =  0 } value (y :: []) (There later) = ?removeElem_rhs_3
-- removeElem {n = (S k)} value (y :: xs) (There later) = y :: removeElem value xs later -- ca 7


-- We pass later as Proof that value is in ys 
-- Look at  the hole of n=0 this case and its Type length of both vectors
-- Case split xs (only one Case Look at the Type)


-- This Code Typechecks so we cant use impossible like in 8
-- For cases like this there is the absurd definiton 

-- absurd : Uninhabited t => t -> a
-- Uninhabited is a interface which can be impplemented for Types that dont have Values E.g EqNat 4 5


Uninhabited (Elem v [])  where
    uninhabited Refl impossible

removeElem:{n:_}->(value:a) -> (xs:Vect (S n) a) -> (prf: Elem value xs) -> Vect n a
removeElem value (value :: xs) Here = xs
removeElem {n =  0 } value (y :: []) (There later) = absurd(later)
removeElem {n = (S k)} value (y :: xs) (There later) = y :: removeElem value xs later -- ca 7



-- AUTO IMPLICIT
-- The Need to provide a proof is very inconvienient and carries everywhere in the code 


removeElemAuto:{n:_}->(value:a) -> (xs:Vect (S n) a) -> {auto  prf: Elem value xs } -> Vect n a
removeElemAuto value xs {prf} = (removeElem value xs prf)

 --This Function finds the Proof using the expression search 

 
-- Decidablity Predicates 
-- A Property is decidable if we can always say wheter the property holds for a given value

isElem : DecEq ty => (value : ty) -> (xs : Vect n ty) -> Dec (Elem value xs)

-- The Types States that for all Decdable inputs we can Decide if  Element is in a Vecttor 

{- Dec 
    Yes :Elem value xs 
    No :(Elem value xs ) -> Void 
-}

-- Writing is Elem (defined in Data.Vect)


isElem' : DecEq ty => (value : ty) -> (xs : Vect n ty) -> Dec (Elem value xs)
{- isElem' value [] = No ?notInNil
isElem' value (x :: xs) = ?isElem'_rhs_1  -}
-- Type of Notnil (Proof that there cant be an element in a empty vect)

{- isElem' value [] = No ?notInNil
isElem' value (x :: xs) = case decEq value x  of 
                               Yes Refl => Yes Here
                               (No contra)=> ?h_1 -}

-- You cant use Her yet look at the Type
-- Value is (=)



isElem' value [] = No ?notInNil
isElem' value (x :: xs) = case decEq value x  of 
                               Yes Refl => Yes Here
                               (No contra)=> case isElem value xs of
                                                  (Yes prf) => Yes ?h3_2
                                                  (No notThere) => No ?notInTail 

-- Searching Proof with expression search h32
-- make Toplevel Function for Not in Nil not in tail
-- Not in Tail is the same as Elem Not in Nl


{- notInTail : (notThere : Elem value xs -> Void) ->
            (notHere : (value = x) -> Void) ->
           Elem value (x :: xs) -> Void
notInTail notThere notHere Here = ?notInTail_rhs_1
notInTail notThere notHere (There later) = ?notInTail_rhs_2 -}

-- It is also possoble to define isElem' without tzhose types like this

elem : Eq ty => (value : ty) -> (xs : Vect n ty) -> Bool
elem value [] = False
elem value (x :: xs) = case value == x of
                            False => elem value xs
                            True => True
