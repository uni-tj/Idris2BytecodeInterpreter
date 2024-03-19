module BytecodeInterpreter
import Data.Vect
import Data.Fin
import Debug.Trace
data Tpe : Type where
  Text : Tpe
  Long : Tpe
  Float : Tpe
  Boolean : Tpe
  HeapType : Tpe
  Vd:Tpe

Locals : Nat -> Type
Locals n = Vect n Tpe

Operands : Nat -> Type
Operands n = Vect n Tpe

data HeapT : Type where 
  ArrayT: (n: Nat) -> Tpe -> HeapT    
  Boxed : Tpe -> HeapT 

data Index : Vect n t -> t -> Type where
  Z : Index (vt :: ts) vt
  S : Index ts vt -> Index (u :: ts) vt
%name Index idx, idx'   

data Value : Tpe -> Type where
  TextValue : String -> Value Text
  LongValue : Int -> Value Long
  FloatValue : Double -> Value Float
  BooleanValue : Bool -> Value Boolean
  MemoryRef : Index hp (t)  -> Value HeapType
  NoValue : Value Vd

%name Value val, val1, val2
Show (Value Text) where
  show (TextValue t) = t
Show (Value Long) where
  show (LongValue l) = show l
Show (Value Boolean) where
  show (BooleanValue l) = show l
Show (Value Vd) where
  show (NoValue) = "NoValue"
namespace Hp
  export
  data MemoryCell: Maybe Tpe -> Type where
    Empty : MemoryCell Nothing 
    Data : Value t -> MemoryCell (Just t)
  export 
  data MemBlock : Fin m -> HeapT -> Type where 
    Block : (s: Fin m) -> Index os bt -> MemBlock s bt  
  public export 
  data Heap :  (fs :Vect bs HeapT)->    (m: Nat) -> (s:Fin (S m))-> Type where 
    
    Nil :(m:Nat) -> Heap []  m $ 0
    (::) :MemBlock s bt -> Heap hp m b -> Heap  (bt :: hp) m (b + s)


size : HeapT -> Nat
size (Boxed _)  = ?a 
size (ArrayT s _) = ?b

data Environment : Vect n t  -> Type where

  Nil : Environment []
  (::) : (v:Value t) -> Environment ts -> Environment (t :: ts)

%name Environment env, env1, env2 
-- This function's type signature is simplified for demonstration purposes.
mergeEnv : Environment xs -> Environment ys -> Environment (xs ++ ys)
mergeEnv Nil env1 = env1
mergeEnv (v :: env) env1 = v :: (mergeEnv env env1)

Num (Value Long) where
  (+) (LongValue x) (LongValue y) = LongValue (x + y)
  (*) (LongValue x) (LongValue y) = LongValue (x * y)
  fromInteger x = LongValue (fromInteger x)

data UnOp : Tpe -> Tpe -> Type where
  Inc: UnOp Long Long
  Dec: UnOp Long Long
  Not : UnOp Boolean Boolean 

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
  -- Add other instruction definitions with explicit types for arguments and return value

  -- data Instruction :Locals l -> Operands i  -> (hp: Hp.Heap ht m s) -> (rhp:Hp.Heap rht m rcs)-> Maybe Tpe -> Type where
  --   Return : Instruction ls (t ::[]) hp hp (Just t)
  --   LoadConstant : Value v -> Instruction ls (v:: os) hp rhp t -> Instruction ls (os) hp rhp t 
  --   BinaryOperation : BinOp it ot -> Instruction ls (ot::os) hp rh t -> Instruction ls (it :: it :: os) hp rh t
  --   UnaryOperation : UnOp it ot -> Instruction ls (ot::os) hp rh t -> Instruction ls ( it :: os) hp rh t
  --   Store : Index ls vt -> Instruction ls os hp rh t -> Instruction ls (vt:: os) hp rh t
  --   Load : Index ls vt -> Instruction ls (vt:: os) hp rh t -> Instruction ls os hp rh t
  --   VoidReturn : Instruction ls [] hp hp (Just Vd)
  --   NoOp : Instruction ls os hp rh rt -> Instruction ls os hp rh rt
  --   Dup : Instruction ls (v :: v::os) hp rh rt -> Instruction ls (v :: os) hp rh rt
  --   FlowBreak :{- Instruction ls os (Just rt) -> -}Instruction ls [] Nothing
  --   Jump :Instruction ls os hp rh rt ->Instruction ls os hp rh rt
  --   CondJump :Instruction ls os hp rh rt -> Instruction ls os hp rh rt -> Instruction ls (Boolean :: os) hp rh  rt
  --   FunctionCall : Func args frt hp rh -> Instruction ls (frt :: []) rh nh rt -> Instruction ls (args) hp nh  rt
  --   If : Instruction ls ([])  hp rh Nothing ->  Maybe (Instruction ls [] hp rh Nothing) -> Instruction ls [] rh nh rt -> Instruction ls (Boolean :: ([])) hp nh  rt 
  --   While: Instruction ls [] (Just Boolean) ->  Instruction ls [] hp rh Nothing -> Instruction ls [] rh nh rt -> Instruction ls [] rh nh rt
  --   Allocate : (t: HeapT) ->  Instruction ls [] (Hp.Heap ((t::ht) m (s+ (natToFin (size t))))) rh rt -> Instruction ls [] (Hp.Heap ht m s) rh rt
  --   Start : Instruction ls [] (Hp.Heap [] 100 0 ) rh -> Instruction ls [] (Hp.Heap [] 100 0 ) rh
    {- If' : {trueRet : Bool} -> {falseRet:Bool} -> Instruction ls ([])  (case trueRet of
                                                                            True => FlowBreakType
                                                                            False => rt) ->  Maybe (Instruction ls [] FlowBreakType) -> Instruction ls [] rt -> Instruction ls (Boolean :: ([])) rt  -}

  data Instruction :(ls: Locals l) -> (os: Operands i) -> (hp: Hp.Heap ht m s) ->  (rhp: Hp.Heap rht' m rcs) -> (rt: Maybe Tpe) -> Type where
    LoadConstant : Value v -> Instruction ls (v :: os) hp rhp t -> Instruction ls (os) hp rhp t
  data Instr' :Locals l -> Operands i  -> Hp.Heap ht m s -> Hp.Heap rht m rcs-> Maybe Tpe -> Type where
    Ret : Instr' ls [t] hp hp (Just t)
    Load : Instr' ls [t] hp rhp (Just t) -> Instr' ls [t] hp rhp (Just t)-- Addig Value v is breaking the TypeChecker
    Load1 : Int-> Instr' ls [t] hp rhp (Just t) -> Instr' ls [] hp rhp (Just t)
    Load2 : Value v -> Instr' ls [v] hp rhp (Just t) -> Instr' ls [] hp rhp (Just t)
    Load3 : Value v -> Instr' ls (v :: os) hp rhp (Just t) -> Instr' ls os hp rhp (Just t)
  data Func: Locals l -> Tpe -> Hp.Heap ht m s -> Hp.Heap rh m rs -> Type where 
    Function :(Environment ls)-> Instruction (args++ls) [] hp rh (Just rt) -> Func args rt hp rh  
%name Func func, func1, func2  

%name Instruction  instr, instr1, instr2   
--
--
-- {-
-- This Function is used to inject a follow up instruction that has A FlowBreak Instruction and no Return Type(Nothing) and a Follow up Instruction 
-- The Function is used for if and while instructions because there might be a Instruction that Follows
--
-- -}
-- injInstr : Instruction ls is hp rh Nothing -> Instruction ls [] rh nh (Just rt) -> Instruction ls (is) hp nh (Just rt)  
-- injInstr (LoadConstant val instr) instr' = LoadConstant val $ injInstr instr instr'
-- injInstr (FlowBreak) instr' = instr'
-- injInstr (BinaryOperation op instr) instr' = BinaryOperation op $ injInstr instr instr'
-- injInstr (UnaryOperation op instr) instr' = UnaryOperation op $ injInstr instr instr'
-- injInstr (If ifinstr elseInstr afterinstr)  instr' = If ifinstr elseInstr $ injInstr afterinstr instr'
-- injInstr (Store idx instr) instr' = Store idx $ injInstr instr instr'
-- injInstr (Load idx instr) instr' = Load idx $ injInstr instr instr'
-- injInstr (FunctionCall func instr) instr'=  FunctionCall func $ injInstr instr instr'
-- -- injInstr Return instr' impossible 
-- injInstr (While cond body after) instr' = While cond body $ injInstr after instr'  
-- injInstr (NoOp instr) instr' = NoOp $ injInstr instr instr'
-- injInstr (Jump instr) instr' = NoOp $ injInstr instr instr'
-- injInstr (Dup instr) instr' = Dup $ injInstr instr instr'
-- injInstr (CondJump tinstr finstr) instr' = CondJump  (injInstr tinstr instr') (injInstr finstr instr')
--
-- -- Adjust lookup and update to work with Vect
-- lookup : Index ts t -> Environment ts -> Value t
-- lookup Z (v :: _) = v
-- lookup (S k) (_ :: vs) = lookup k vs
-- --
-- update : Index ts t -> Value t -> Environment ts -> Environment ts
-- update Z newVal (_ :: vs) = newVal :: vs
-- update (S n) newVal (v :: vs) = v :: update n newVal vs
-- performUnOp : UnOp it ot -> Value it -> Value ot
-- performUnOp Inc (LongValue i) = (LongValue (i+1))
-- performUnOp Not (BooleanValue b) = (BooleanValue (not b))
-- performUnOp Dec (LongValue i) = (LongValue (i-1))
--
-- performBinOp : BinOp it ot -> Value it -> Value it -> Value ot
-- performBinOp Append (TextValue i) (TextValue j) = TextValue (i ++ j)
-- performBinOp Add (LongValue i) (LongValue j) = LongValue (i + j)
-- performBinOp Sub  (LongValue i) (LongValue j)= (LongValue (i-j))
-- performBinOp Mul (LongValue i) (LongValue j) = LongValue (i*j)
-- performBinOp Div (LongValue i) (LongValue j) = LongValue (i `div` j)
-- performBinOp Mod (LongValue i) (LongValue j) = LongValue (i `mod` j)
-- performBinOp LtEq (LongValue i) (LongValue j) = BooleanValue ( i <= j)
-- performBinOp GtEq (LongValue i) (LongValue j) = (BooleanValue (i>= j))
-- performBinOp Eq (LongValue i) (LongValue j) = BooleanValue (i==j)
-- performBinOp Lt (LongValue i) (LongValue j) = BooleanValue (i < j) 
-- performBinOp Gt (LongValue i) (LongValue j) = BooleanValue (i> j)
-- performBinOp LOR (BooleanValue b1) (BooleanValue b2) = BooleanValue (b1 || b2)
-- performBinOp LAND (BooleanValue b1) (BooleanValue b2) = BooleanValue (b1 && b2)
-- performBinOp LXOR (BooleanValue b1) (BooleanValue b2) = BooleanValue (b1 /=b2)
--
-- performBinOp AddF (FloatValue i) (FloatValue j) = FloatValue (i + j)
-- performBinOp SubF (FloatValue i) (FloatValue j)= (FloatValue (i-j))
-- performBinOp MulF (FloatValue i) (FloatValue j) = FloatValue (i*j)
-- performBinOp DivF (FloatValue i) (FloatValue j) = FloatValue (i / j)
-- performBinOp LtEqF (FloatValue i) (FloatValue j) = BooleanValue ( i <= j)
-- performBinOp GtEqF (FloatValue i) (FloatValue j) = (BooleanValue (i>= j))
-- performBinOp EqF (FloatValue i) (FloatValue j) = BooleanValue (i==j)
-- performBinOp LtF (FloatValue i) (FloatValue j) = BooleanValue (i < j) 
-- performBinOp GtF (FloatValue i) (FloatValue j) = BooleanValue (i> j)
--
-- {- splitEnv : {v: Vect (n+m) Tpe}->  {v1: Vect n Tpe} -> {v2:Vect (m) Tpe}-> (n:Nat) -> (m:Nat) -> Environment v  -> (Environment (v1), Environment v2)
--
-- splitEnv' : {n:Nat}->{bs:Vect (plus n m) t}->{os : Vect n t} -> {is : Vect m t} ->{auto prf: os ++ is = bs} ->Environment (bs)  -> (Environment os, Environment is)
-- splitEnv' {n = 0} env = (Nil , rewrite (Refl :Vect 0 t ++ Vect m t  = Vect m t) env)
-- splitEnv' {n = (S k)} env = ?splitEnv'_rhs_1 -}
--
--
-- interpret :Instruction ls os (Just t) -> Environment ls -> Environment os->  Value t
-- interpret (LoadConstant v instr) locals oStack = (interpret instr locals (v:: oStack))
-- interpret (BinaryOperation op instr) locals (v1:: v2::  oStack) = interpret instr locals ((performBinOp op v2 v1) :: oStack ) 
-- interpret (UnaryOperation op instr) locals (v::  oStack) = interpret instr locals ((performUnOp op v) :: oStack ) 
-- interpret Return locals (v::[]) = v 
-- interpret VoidReturn locals [] = NoValue
-- interpret FlowBreak locals os impossible 
-- interpret (If trueInstr (Just elseInstr) afterInstr) locals ((BooleanValue b) :: oStack) = interpret (case b of
--                                                                                           False => (injInstr trueInstr afterInstr)
--                                                                                           True => (injInstr trueInstr afterInstr)) locals oStack
-- interpret (If trueInstr Nothing afterInstr) locals ((BooleanValue b) :: oStack) = interpret (case b of
--                                                                                           False => afterInstr
--                                                                                           True => (injInstr trueInstr afterInstr)) locals oStack
-- interpret (Store idx instr) locals (v:: oStack) = interpret instr (update idx v locals) oStack
-- interpret (Load idx instr) locals oStack = interpret instr locals $ (lookup idx locals) :: oStack
-- interpret (FunctionCall (Function ls instr) afterInstr) locals oStack = 
--   let funcRes = interpret instr (mergeEnv oStack  ls) [] 
--   in (interpret afterInstr locals [funcRes])
-- interpret w@(While cond body after) locals oStack = case (interpret cond locals oStack) of
--                                                        (BooleanValue False) => (interpret after locals oStack)
--                                                        (BooleanValue True) => interpret (injInstr body w) locals oStack
-- interpret (NoOp instr) locals oStack = interpret instr locals oStack
-- interpret (Jump instr) locals oStack = interpret instr locals oStack
-- interpret (CondJump tinstr finstr) locals (b :: oStack)  = case b of
--                                                                 (BooleanValue True) => interpret tinstr locals oStack
--                                                                 (BooleanValue False) => interpret finstr locals oStack
-- interpret (Dup instr) locals (v::oStack) = interpret instr locals $ v::v::oStack
--   
--
-- example :(Instruction [] [] (Just Boolean) )
-- prf : Index [Boolean, Long, Boolean] Long
-- prf = S Z
--
-- flowbreakexample: (Instruction [Boolean, Long, Boolean] [] Nothing) 
-- flowbreakexample = LoadConstant (LongValue 42) $ (Store prf FlowBreak)
-- afterInstr = Load prf $ Return 
-- ifexample : (Instruction [Boolean, Long, Boolean] [] (Just Long))
-- ifexample =LoadConstant (LongValue 10) $   Store prf $LoadConstant (BooleanValue True) ( 
--                        If flowbreakexample Nothing (afterInstr ))
-- locals = [(BooleanValue True), (LongValue 0), (BooleanValue False) ]
-- examplefunc : Func [Long, Long] Long
-- examplefunc = Function Nil (Load (S Z) $ Load Z $ BinaryOperation Add $ LoadConstant (LongValue 42) $ BinaryOperation Mul $ Return) 
-- {- simpleExampleFunc : Func [Long] Long
-- simpleExampleFunc = Function Nil (LoadConstant (LongValue 42) Return) -}
--
--
-- whileExample: Instruction [Long] [] (Just Long )
-- whileExample = While (Load Z (LoadConstant (LongValue 10) (BinaryOperation Lt Return))) (Load Z (UnaryOperation Inc (Store Z (FlowBreak))) ) (Load (Z) Return)
--
-- {- Show (Value FlowBreakType) where
--   show (FlowBreakValue) = "FlowBreak" -}
--
-- fullFuncExample : Instruction [] [] (Just Long)
-- fullFuncExample = (LoadConstant (LongValue 1) $ LoadConstant (LongValue 2) $  (FunctionCall examplefunc  Return ))
--
-- e : Value Long
-- e  = interpret whileExample [0] []
--
