module BytecodeInterpreter
import Data.Vect
import Data.Fin
import Debug.Trace
-- Data Types that can be Pushed on the Stack and Saved in a Variables 
data Tpe : Type where
  Text : Tpe
  Long : Tpe
  Float : Tpe
  Boolean : Tpe
  HeapType : Tpe -- Memory Reference Type 
  Vd:Tpe -- Void Type for Empty Returns

-- Types for the Heap on feature/heap
data HeapT : Type where 
  ArrayT: (n: Nat) -> Tpe -> HeapT    
  Boxed : Tpe -> HeapT 

Locals : Nat -> Type
Locals n = Vect n Tpe

Operands : Nat -> Type
Operands n = Vect n Tpe

-- Index for accesing 
data Index : Vect n t -> t -> Type where
  Z : Index (vt :: ts) vt
  S : Index ts vt -> Index (u :: ts) vt
%name Index idx, idx'   

-- Values of Type Tpe 
data Value : Tpe -> Type where
  TextValue : String -> Value Text
  LongValue : Int -> Value Long
  FloatValue : Double -> Value Float
  BooleanValue : Bool -> Value Boolean
  MemoryRef : Index hp t  -> Value HeapType -- A Memory Reference onto the Heap
  NoValue : Value Vd -- Void / Null Value 

%name Value val, val1, val2
-- Show instance for displaying Values in the console
Show (Value Text) where
  show (TextValue t) = t
Show (Value Long) where
  show (LongValue l) = show l
Show (Value Boolean) where
  show (BooleanValue l) = show l
Show (Value Vd) where
  show (NoValue) = "NoValue"

-- Heap Datatypes that are not in use on this branch 
namespace Heap
  -- A Memory Cell that can be Empty or can hold one value
  data MemoryCell: Maybe Tpe -> Type where
    Empty : MemoryCell Nothing 
    Data : Value t -> MemoryCell (Just t)
  -- A Block of Memory Cells that holds a "Value" of HeapT
  data MemBlock : Fin m -> HeapT -> Type where 
    Block : (s: Fin m) -> Index os bt -> MemBlock s bt  

  -- The Heap that consist of a Vect of Memory Blocks
  data Heap :  Vect bs HeapT->    (m: Nat) -> (s:Fin (S m))-> Type where 
    Nil :(m:Nat) -> Heap []  m $ 0
    (::) :MemBlock s bt -> Heap hp m b -> Heap  (bt :: hp) m (b + s)


-- The Environment that Holds a List of Values of Tpe 
data Environment : Vect n t  -> Type where
  Nil : Environment []
  (::) : (v:Value t) -> Environment ts -> Environment (t :: ts)
%name Environment env, env1, env2 

-- Function For Merging Environments 
mergeEnv : Environment xs -> Environment ys -> Environment (xs ++ ys)
mergeEnv Nil env1 = env1
mergeEnv (v :: env) env1 = v :: (mergeEnv env env1)
--Split Environment into two Environment
splitEnv : {os : Vect n t} ->Environment (os++is)  -> (Environment os, Environment is)
splitEnv {os = []} env = ([], env)
splitEnv {os = (x :: xs)} (v::env) = case (splitEnv env) of
                                     (os', is') => ((v::os'), is')
Num (Value Long) where
  (+) (LongValue x) (LongValue y) = LongValue (x + y)
  (*) (LongValue x) (LongValue y) = LongValue (x * y)
  fromInteger x = LongValue (fromInteger x)

-- Operator Defintions for Unary Operations 
data UnOp : Tpe -> Tpe -> Type where
  Inc: UnOp Long Long
  Dec: UnOp Long Long
  Not : UnOp Boolean Boolean 

-- Operator Defintion for Binary Operations
data BinOp: Tpe -> Tpe -> Type where
  Append: BinOp Text Text
  Add : BinOp Long Long 
  Sub : BinOp Long Long 
  Mul :BinOp Long Long 
  Div :  BinOp Long Long 
  Mod :  BinOp Long Long 
  
  LtEq :  BinOp Long Boolean 
  GtEq :  BinOp Long Boolean 
  Eq :  BinOp Long Boolean 
  Lt :  BinOp Long Boolean 
  Gt :  BinOp Long Boolean 

  AddF : BinOp Float Float 
  SubF : BinOp Float Float 
  MulF :BinOp Float Float 
  DivF :  BinOp Float Float 
  
  LtEqF :  BinOp Float Boolean 
  GtEqF :  BinOp Float Boolean 
  EqF :  BinOp Float Boolean 
  LtF :  BinOp Float Boolean 
  GtF :  BinOp Float Boolean 

  LOR : BinOp Boolean Boolean
  LAND : BinOp Boolean Boolean
  LXOR : BinOp Boolean Boolean

mutual 
  -- Definitions for Different Instructions 
  data Instruction : Locals l -> Operands i   -> Maybe Tpe -> Type where
    LoadConstant : Value v -> Instruction ls (v:: os) t -> Instruction ls (os) t -- Load a constant value onto the stack
    BinaryOperation : BinOp it ot -> Instruction ls (ot::os) t -> Instruction ls (it :: it :: os) t -- Perform a BinaryOperation with to values on the stack
    UnaryOperation : UnOp it ot -> Instruction ls (ot::os) t -> Instruction ls ( it :: os) t -- Perform a UnaryOperation with to values on the stack
    Store : Index ls vt -> Instruction ls os t -> Instruction ls (vt:: os) t -- Store the first value on the stack into a variable by the index proof provided
    Load : Index ls vt -> Instruction ls (vt:: os) t -> Instruction ls os t -- Load a Value from a variable by the index proof provided onto the stack
    Return : Instruction ls (t ::[]) (Just t) -- Return the last value on the stack
    VoidReturn : Instruction ls [] (Just Vd) -- Return Void 
    NoOp : Instruction ls os rt -> Instruction ls os rt -- Perform no operation do not change the stack 
    Dup : Instruction ls (v :: v::os) rt -> Instruction ls (v :: os) rt -- Duplicate the value on top of the stack
    FlowBreak :{- Instruction ls os (Just rt) -> -}Instruction ls [] Nothing -- Used as a JoinPoint for if, while Instructions to concatenate Instructions
    -- Jump :Instruction ls os rt ->Instruction ls os rt -- Jump to a Specific Instruction
    -- CondJump :Instruction ls os rt -> Instruction ls os rt -> Instruction ls (Boolean :: os) rt-- Conditional Jump to a Specific Instruction
    FunctionCall : {args: (Locals l) }->Func args frt -> Instruction ls (frt :: os) rt -> Instruction ls (args ++ os)  rt -- Call a Function from a provided Func Instance
    If : Instruction ls ([])  Nothing ->  Maybe (Instruction ls [] Nothing) -> Instruction ls [] rt -> Instruction ls (Boolean :: ([])) rt  -- If instruction takes a Boolean from the Stack and Evaluetes the Possible Branches
    While: Instruction ls [] (Just Boolean) ->  Instruction ls [] Nothing -> Instruction ls [] rt -> Instruction ls [] rt -- While Instruction takes a Condition that is evaluated repeatedly and if the Condition is not True the Body is executed

  data Func: Locals l -> Tpe -> Type where 
    Function :(Environment ls)-> Instruction (args++ls) [] (Just rt) -> Func args rt  
%name Instruction  instr, instr1, instr2   
%name Func func, func1, func2  



{-
This Function is used to inject a follow up instruction that has A FlowBreak Instruction and no Return Type(Nothing) and a Follow up Instruction 
The Function is used for if and while instructions because there might be a Instruction that Follows
-}
injInstr : Instruction ls  is Nothing -> Instruction ls [] (Just rt) -> Instruction ls (is) (Just rt)  
injInstr (LoadConstant val instr) instr' = LoadConstant val $ injInstr instr instr'
injInstr (FlowBreak) instr' = instr'
injInstr (BinaryOperation op instr) instr' = BinaryOperation op $ injInstr instr instr'
injInstr (UnaryOperation op instr) instr' = UnaryOperation op $ injInstr instr instr'
injInstr (If ifinstr elseInstr afterinstr)  instr' = If ifinstr elseInstr $ injInstr afterinstr instr'
injInstr (Store idx instr) instr' = Store idx $ injInstr instr instr'
injInstr (Load idx instr) instr' = Load idx $ injInstr instr instr'
injInstr (FunctionCall func instr) instr'=  FunctionCall func $ injInstr instr instr'
-- injInstr Return instr' impossible 
injInstr (While cond body after) instr' = While cond body $ injInstr after instr'  
injInstr (NoOp instr) instr' = NoOp $ injInstr instr instr'
{- injInstr (Jump instr) instr' = NoOp $ injInstr instr instr'
injInstr (CondJump tinstr finstr) instr' = CondJump  (injInstr tinstr instr') (injInstr finstr instr') -}
injInstr (Dup instr) instr' = Dup $ injInstr instr instr'

--lookup a Value in the Variables by a given Proof
lookup : Index ts t -> Environment ts -> Value t
lookup Z (v :: _) = v
lookup (S k) (_ :: vs) = lookup k vs

-- Update a Variable given a Proof and Value
update : Index ts t -> Value t -> Environment ts -> Environment ts
update Z newVal (_ :: vs) = newVal :: vs
update (S n) newVal (v :: vs) = v :: update n newVal vs
--Execute a UnaryOperation
performUnOp : UnOp it ot -> Value it -> Value ot
performUnOp Inc (LongValue i) = (LongValue (i+1))
performUnOp Not (BooleanValue b) = (BooleanValue (not b))
performUnOp Dec (LongValue i) = (LongValue (i-1))

--Execute BinaryOpertation
performBinOp : BinOp it ot -> Value it -> Value it -> Value ot
performBinOp Append (TextValue i) (TextValue j) = TextValue (i ++ j)
performBinOp Add (LongValue i) (LongValue j) = LongValue (i + j)
performBinOp Sub  (LongValue i) (LongValue j)= (LongValue (i-j))
performBinOp Mul (LongValue i) (LongValue j) = LongValue (i*j)
performBinOp Div (LongValue i) (LongValue j) = LongValue (i `div` j)
performBinOp Mod (LongValue i) (LongValue j) = LongValue (i `mod` j)
performBinOp LtEq (LongValue i) (LongValue j) = BooleanValue ( i <= j)
performBinOp GtEq (LongValue i) (LongValue j) = (BooleanValue (i>= j))
performBinOp Eq (LongValue i) (LongValue j) = BooleanValue (i==j)
performBinOp Lt (LongValue i) (LongValue j) = BooleanValue (i < j) 
performBinOp Gt (LongValue i) (LongValue j) = BooleanValue (i> j)
performBinOp LOR (BooleanValue b1) (BooleanValue b2) = BooleanValue (b1 || b2)
performBinOp LAND (BooleanValue b1) (BooleanValue b2) = BooleanValue (b1 && b2)
performBinOp LXOR (BooleanValue b1) (BooleanValue b2) = BooleanValue (b1 /=b2)

performBinOp AddF (FloatValue i) (FloatValue j) = FloatValue (i + j)
performBinOp SubF (FloatValue i) (FloatValue j)= (FloatValue (i-j))
performBinOp MulF (FloatValue i) (FloatValue j) = FloatValue (i*j)
performBinOp DivF (FloatValue i) (FloatValue j) = FloatValue (i / j)
performBinOp LtEqF (FloatValue i) (FloatValue j) = BooleanValue ( i <= j)
performBinOp GtEqF (FloatValue i) (FloatValue j) = (BooleanValue (i>= j))
performBinOp EqF (FloatValue i) (FloatValue j) = BooleanValue (i==j)
performBinOp LtF (FloatValue i) (FloatValue j) = BooleanValue (i < j) 
performBinOp GtF (FloatValue i) (FloatValue j) = BooleanValue (i> j)



interpret :Instruction ls os (Just t) -> Environment ls -> Environment os->  Value t
interpret (LoadConstant v instr) locals oStack = (interpret instr locals (v:: oStack))
interpret (BinaryOperation op instr) locals (v1:: v2::  oStack) = interpret instr locals ((performBinOp op v2 v1) :: oStack ) 
interpret (UnaryOperation op instr) locals (v::  oStack) = interpret instr locals ((performUnOp op v) :: oStack ) 
interpret Return locals (v::[]) = v 
interpret VoidReturn locals [] = NoValue
interpret FlowBreak locals os impossible 
interpret (If trueInstr (Just elseInstr) afterInstr) locals ((BooleanValue b) :: oStack) = interpret (case b of
                                                                                          False => (injInstr trueInstr afterInstr)
                                                                                          True => (injInstr trueInstr afterInstr)) locals oStack
interpret (If trueInstr Nothing afterInstr) locals ((BooleanValue b) :: oStack) = interpret (case b of
                                                                                          False => afterInstr
                                                                                          True => (injInstr trueInstr afterInstr)) locals oStack
interpret (Store idx instr) locals (v:: oStack) = interpret instr (update idx v locals) oStack
interpret (Load idx instr) locals oStack = interpret instr locals $ (lookup idx locals) :: oStack
interpret (FunctionCall (Function ls instr) afterInstr) locals oStack = 
  let (args, oStack')= (splitEnv oStack)
      funcRes = interpret instr (mergeEnv args  ls) [] 
  in (interpret afterInstr locals (funcRes :: oStack'))
interpret w@(While cond body after) locals oStack = case (interpret cond locals oStack) of
                                                       (BooleanValue False) => (interpret after locals oStack)
                                                       (BooleanValue True) => interpret (injInstr body w) locals oStack
interpret (NoOp instr) locals oStack = interpret instr locals oStack
interpret (Dup instr) locals (v::oStack) = interpret instr locals $ v::v::oStack
  
-- Some Basic Examples 
example :(Instruction [] [] (Just Boolean) )
prf : Index [Boolean, Long, Boolean] Long
prf = S Z

flowbreakexample: (Instruction [Boolean, Long, Boolean] [] Nothing) 
flowbreakexample = LoadConstant (LongValue 42) $ (Store prf FlowBreak)

afterInstr = Load prf $ Return 

ifexample : (Instruction [Boolean, Long, Boolean] [] (Just Long))
ifexample =LoadConstant (LongValue 10) $   Store prf $LoadConstant (BooleanValue True) ( 
                       If flowbreakexample Nothing (afterInstr ))

locals = [(BooleanValue True), (LongValue 0), (BooleanValue False) ]

examplefunc : Func [Long, Long] Long
examplefunc = Function Nil (Load (S Z) $ Load Z $ BinaryOperation Add $ LoadConstant (LongValue 42) $ BinaryOperation Mul $ Return) 

simpleExampleFunc : Func [Long] Long
simpleExampleFunc = Function Nil (LoadConstant (LongValue 42) Return) 

whileExample: Instruction [Long] [] (Just Long )
whileExample = While (Load Z (LoadConstant (LongValue 10) (BinaryOperation Lt Return))) (Load Z (UnaryOperation Inc (Store Z (FlowBreak))) ) (Load (Z) Return)

{- Show (Value FlowBreakType) where
  show (FlowBreakValue) = "FlowBreak" -}

fullFuncExample : Instruction [] [] (Just Long)
fullFuncExample = (LoadConstant (LongValue 1) $ LoadConstant (LongValue 2) $  (FunctionCall examplefunc  Return ))

e : Value Long
e  = interpret whileExample [0] []

