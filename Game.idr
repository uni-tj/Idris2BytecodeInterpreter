module Game 

import Data.String
import Data.Vect
import Data.Vect.Elem
import Decidable.Equality
-- Aus Main.idr
total
removeElemAuto : {n : _} ->
             (value : a) -> (xs : Vect (S n) a) ->
             {auto prf : Elem value xs} ->
             Vect n a
removeElemAuto value (value :: ys) {prf = Here} = ys
removeElemAuto {n = Z} value (y :: []) {prf = There later} = absurd later
removeElemAuto {n = (S k)} value (y :: ys) {prf = There later}
                                  = y :: removeElemAuto value ys
-- Ende Main
data WordState : (guesses : Nat) -> (letters : Nat) -> Type where
     MkWordState : (word : String)
                   -> (missing : Vect letters Char)
                   -> WordState guesses_remaining letters

data Finished : Type where
     Lost : (game : WordState 0 (S letters)) -> Finished
     Won  : (game : WordState (S guesses) 0) -> Finished

-- game: WordState (S guesses ) (S letters) -> IO Finished

-- We want to read the User Input bu want only valid inputs 

data ValidInput : List Char -> Type where
     Letter : (c : Char) -> ValidInput [c]


isValidNil : ValidInput [] -> Void
isValidNil (Letter _) impossible

isValidTwo : ValidInput (x :: (y :: xs)) -> Void
isValidTwo (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No isValidNil
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: (y :: xs)) = No isValidTwo

-- Unpack takes a String and turns it into a list of chars
isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

-- Returning a dependent pair we express the Postconditon that the return Value is a Valid Inpu
readGuess : IO (x ** ValidInput x)
readGuess = do putStr "Guess: "
               x <- getLine
               case isValidString (toUpper x) of
                    Yes prf => pure (_ ** prf)
                    No contra => do putStrLn "Invalid guess"
                                    readGuess
-- This Type expresses for any Guess we can change 
processGuess: (letter:Char)-> 
              (WordState (S guesses)  (S letters)) ->
              Either  (WordState guesses (S letters))-- Wrong Guess
                      (WordState (S guesses) letters)-- Right Guess

-- Generate Definiton using ca 
{- processGuess letter (MkWordState word missing) = case isElem letter missing of
                                                      (Yes prf) => Right (MkWordState word ?nextVect)-- (removeElemAuto letter Missing)
                                                      (No contra) => Left (MkWordState word missing) -}

 
-- Der Typ sichert zu dass nie ein unzulssiger zustand Ensteht oder der Zustand sich Falsch nert



game : {guesses : _} -> {letters : _} ->
       WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} st
        = do (_ ** Letter letter) <- readGuess
             case processGuess letter st of
                  Left l => do putStrLn ("Wrong! " ++ show guesses ++
                                         " guesses remaining")
                               case guesses of
                                    Z => pure (Lost l)
                                    S k => game l
                  Right r => do putStrLn "Right!"
                                case letters of
                                     Z => pure (Won r)
                                     S k => game r

main : IO ()
main = do result <- game {guesses=2} (MkWordState "Test" ['T', 'E', 'S'])
          case result of
               Lost (MkWordState word missing) =>
                    putStrLn ("You lose. The word was " ++ word)
               Won game =>
                    putStrLn "You win!"
