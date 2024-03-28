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
{- interface HeapTToVect (hpT : HeapT) where
  heapTToVect : hpT -> Vect n Value
  VectToHeapT : Vect n -> hpT  -}
size : (m : Nat ) ->HeapT -> Fin (S m) 
size _ (Boxed _)  = 0
size _ (ArrayT s _) = 0

natSize : HeapT -> Nat
natSize (Boxed _)  = 1
natSize (ArrayT s _) = s
namespace Hp
  public export
  data MemoryCell: Type where
    Empty : MemoryCell
    Data : Value t -> MemoryCell 
  public export 
  data MemBlock :  Fin m -> HeapT -> Type where 
    Block : (s: Fin (S m)) -> Vect (natSize bt) MemoryCell ->  MemBlock (s) bt  
  public export 
  data Heap :  (fs :Vect bs HeapT)->    (m: Nat) -> (s:Fin (S m))-> Type where 
    
    Nil :(m:Nat) -> Heap []  m  0
    (::) :MemBlock  s bt -> Heap hp m b -> Heap  (hp++[bt]) m (s+b )


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

  data Instruction :Locals l -> Operands i  -> (hp: Hp.Heap ht m s) -> (rhp:Hp.Heap rht m rcs)-> Maybe Tpe -> Type where
    Return : Instruction ls (t ::[]) hp hp (Just t)
    LoadConstant : {0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}->Value v -> Instruction ls (v:: os) hp rhp t -> Instruction ls (os) hp rhp t 
    BinaryOperation :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}-> BinOp it ot -> Instruction ls (ot::os) hp rhp t -> Instruction ls (it :: it :: os) hp rhp t
    UnaryOperation :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rhpt m rcs}-> UnOp it ot -> Instruction ls (ot::os) hp rhp t -> Instruction ls ( it :: os) hp rhp t
    Store :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}-> Index ls vt -> Instruction ls os hp rhp t -> Instruction ls (vt:: os) hp rhp t
    Load :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}-> Index ls vt -> Instruction ls (vt:: os) hp rhp t -> Instruction ls os hp rhp t
    VoidReturn :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}-> Instruction ls [] hp hp (Just Vd)
    NoOp :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}-> Instruction ls os hp rhp rt -> Instruction ls os hp rhp rt
    Dup :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}-> Instruction ls (v :: v::os) hp rhp rt -> Instruction ls (v :: os) hp rhp rt
    FlowBreak :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}->{- Instruction ls os (Just rt) -> -}Instruction ls [] hp hp Nothing
    Jump :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}->Instruction ls os hp rhp rt ->Instruction ls os hp rhp rt
    CondJump :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}->Instruction ls os hp rhp rt -> Instruction ls os hp rhp rt -> Instruction ls (Boolean :: os) hp rhp  rt
    FunctionCall :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}->{0 nhp: Hp.Heap rht m rcs} ->{args:Vect n Tpe}->Func args frt hp rhp -> Instruction ls (frt :: sos) rhp nhp rt -> Instruction ls (args++sos) hp nhp  rt
    If :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}->{0 nhp: Hp.Heap rht m rcs}-> Instruction ls ([])  hp rhp Nothing ->  Maybe (Instruction ls [] hp rhp Nothing) -> Instruction ls [] rhp nhp rt -> Instruction ls (Boolean :: ([])) hp nhp  rt 
    While:{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}-> {0 nhp: Hp.Heap rht m rcs}-> Instruction ls [] hp hp(Just Boolean) ->  Instruction ls [] hp rhp Nothing -> Instruction ls [] rhp nhp rt -> Instruction ls [] rhp nhp rt
    Allocate : {m:Nat}->{s:Fin (S m)}-> {rcs:Fin (S m)}->{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}->{nhp: Hp.Heap (t:: rht) m ( (size m t)+  s)}-> HeapT->Instruction ls os nhp rhp rt -> Instruction ls os hp rhp rt
    -- Allocate :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}-> (t: HeapT) ->  Instruction ls [] ?hap {- (Hp.Heap (t::ht) m ?sk (plus ?s ?k)) -} rhp rt -> Instruction ls [] ?rhap{- (Hp.Heap ht m s) -} rhp rt
    {- If' : {trueRet : Bool} -> {falseRet:Bool} -> Instruction ls ([])  (case trueRet of
                                                                            True => FlowBreakType
                                                                            False => rt) ->  Maybe (Instruction ls [] FlowBreakType) -> Instruction ls [] rt -> Instruction ls (Boolean :: ([])) rt  -}

  data Func: Locals l -> Tpe -> Hp.Heap ht m s -> Hp.Heap rh m rs -> Type where 
    Function :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}->(Environment ls)-> Instruction (args++ls) [] hp rhp (Just rt) -> Func args rt hp rhp  
%name Func func, func1, func2  

%name Instruction  instr, instr1, instr2   


{-
This Function is used to inject a follow up instruction that has A FlowBreak Instruction and no Return Type(Nothing) and a Follow up Instruction 
The Function is used for if and while instructions because there might be a Instruction that Follows

-}
injInstr :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}->{0 nhp: Hp.Heap rht m rcs}-> Instruction ls is hp nhp Nothing -> Instruction ls [] nhp rhp (Just rt) -> Instruction ls (is) hp rhp (Just rt)  
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
injInstr (Jump instr) instr' = NoOp $ injInstr instr instr'
injInstr (Dup instr) instr' = Dup $ injInstr instr instr'
injInstr (CondJump tinstr finstr) instr' = CondJump  (injInstr tinstr instr') (injInstr finstr instr')

-- Adjust lookup and update to work with Vect
lookup : Index ts t -> Environment ts -> Value t
lookup Z (v :: _) = v
lookup (S k) (_ :: vs) = lookup k vs
--
update : Index ts t -> Value t -> Environment ts -> Environment ts
update Z newVal (_ :: vs) = newVal :: vs
update (S n) newVal (v :: vs) = v :: update n newVal vs
performUnOp : UnOp it ot -> Value it -> Value ot
performUnOp Inc (LongValue i) = (LongValue (i+1))
performUnOp Not (BooleanValue b) = (BooleanValue (not b))
performUnOp Dec (LongValue i) = (LongValue (i-1))

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
performBinOp GtF (FloatValue i) (FloatValue j) = BooleanValue (i > j)

{- splitEnv : {v: Vect (n+m) Tpe}->  {v1: Vect n Tpe} -> {v2:Vect (m) Tpe}-> (n:Nat) -> (m:Nat) -> Environment v  -> (Environment (v1), Environment v2)

splitEnv' : {n:Nat}->{bs:Vect (plus n m) t}->{os : Vect n t} -> {is : Vect m t} ->{auto prf: os ++ is = bs} ->Environment (bs)  -> (Environment os, Environment is)
splitEnv' {n = 0} env = (Nil , rewrite (Refl :Vect 0 t ++ Vect m t  = Vect m t) env)
splitEnv' {n = (S k)} env = ?splitEnv'_rhs_1 -}
splitEnv : {is : Vect n t} -> Environment (is ++ os) -> (Environment is , Environment os)
splitEnv {is = []} env = ([], env)
splitEnv {is = (x :: xs)} (v ::env) = case (splitEnv env) of
                                     (eis, eos) => (v:: eis , eos)
constructHeapIdx : (ht : HeapT) -> Hp.Heap hp m cs -> Index (ht :: hp) ht

createEmptyMemoryCells : (n:Nat) -> Vect n (MemoryCell)
createEmptyMemoryCells 0 = []
createEmptyMemoryCells (S k) = Empty :: createEmptyMemoryCells k 

constructHeapBlock: {m:Nat} -> {cs:Fin (S m)} ->  (ht:HeapT) -> Hp.Heap hp m cs -> Hp.MemBlock (size m ht) ht 
constructHeapBlock  {m} ht hp = Block (size m ht) content 
                                where 
                                  content = createEmptyMemoryCells $ natSize ht 

allocateMem : {m:Nat} -> {cs:Fin (S m)} -> {hp:Vect n HeapT}->(t:HeapT) -> Hp.Heap hp m cs -> Hp.Heap (hp++[t]) m $(size m t ) + cs
allocateMem ht heap = (constructHeapBlock ht heap ) :: heap

interpret :{0 hp: Hp.Heap ht m s}->{0 rhp: Hp.Heap rht m rcs}->Instruction ls os hp rhp (Just t) -> Environment ls -> Environment os->  Value t
interpret (LoadConstant v instr) locals oStack = (interpret instr locals (v:: oStack))
interpret (BinaryOperation op instr) locals (v1:: v2::  oStack) = interpret instr locals ((performBinOp op v2 v1) :: oStack ) 
interpret (UnaryOperation op instr) locals (v::  oStack) = interpret instr locals ((performUnOp op v) :: oStack ) 
interpret Return locals (v::[]) = v 
interpret VoidReturn locals [] = NoValue
interpret FlowBreak locals os impossible 
interpret (If trueInstr (Just elseInstr) afterInstr) locals ((BooleanValue b) :: oStack) = case b of
                                                                                          False => let instr = injInstr elseInstr afterInstr --(injInstr trueInstr afterInstr)
                                                                                                    in (interpret instr locals oStack)
                                                                                          True => let instr = injInstr trueInstr afterInstr--(injInstr trueInstr afterInstr)
                                                                                                  in (interpret instr locals oStack)
interpret (If trueInstr Nothing afterInstr) locals ((BooleanValue b) :: oStack) = case b of
                                                                                          False => interpret afterInstr locals oStack --afterInstr
                                                                                          True => interpret (injInstr trueInstr afterInstr) locals oStack
interpret (Store idx instr) locals (v:: oStack) = interpret instr (update idx v locals) oStack
interpret (Load idx instr) locals oStack = interpret instr locals $ (lookup idx locals) :: oStack
interpret (FunctionCall (Function ls instr) afterInstr) locals oStack = 
  let 
    (fargs, aStack) = (splitEnv oStack)
    funcRes = interpret instr (mergeEnv fargs  ls) [] 
  in (interpret afterInstr locals (funcRes::aStack))
interpret w@(While cond body after) locals oStack = case (interpret cond locals oStack) of
                                                       (BooleanValue False) => (interpret after locals oStack)
                                                       (BooleanValue True) => interpret (injInstr body w) locals oStack
interpret (NoOp instr) locals oStack = interpret instr locals oStack
interpret (Jump instr) locals oStack = interpret instr locals oStack
interpret (CondJump tinstr finstr) locals (b :: oStack)  = case b of
                                                                (BooleanValue True) => interpret tinstr locals oStack
                                                                (BooleanValue False) => interpret finstr locals oStack
interpret (Dup instr) locals (v::oStack) = interpret instr locals $ v::v::oStack
interpret (Allocate hpt instr) locals oStack = ?interpret_missing_case_1
  

example :(Instruction [] [] hp rhp(Just Boolean) )
prf : Index [Boolean, Long, Boolean] Long
prf = S Z

flowbreakexample: (Instruction [Boolean, Long, Boolean] [] (Nil 0) (Nil 0) Nothing) 
flowbreakexample = LoadConstant (LongValue 42) $ (Store prf FlowBreak)
afterInstr = Load prf $ Return 
ifexample : (Instruction [Boolean, Long, Boolean] [] (Nil 0) (Nil 0) (Just Long))
ifexample =LoadConstant (LongValue 10) $   Store prf $LoadConstant (BooleanValue True) ( 
                       If flowbreakexample Nothing (afterInstr ))
locals = [(BooleanValue True), (LongValue 0), (BooleanValue False) ]
examplefunc : Func [Long, Long] Long (Nil 0) (Nil 0)
examplefunc = Function Nil (Load (S Z) $ Load Z $ BinaryOperation Add $ LoadConstant (LongValue 42) $ BinaryOperation Mul $ Return) 
{- simpleExampleFunc : Func [Long] Long
simpleExampleFunc = Function Nil (LoadConstant (LongValue 42) Return) -}


whileExample: Instruction [Long] [] (Nil 0) (Nil 0) (Just Long )
whileExample = While (Load Z (LoadConstant (LongValue 10) (BinaryOperation Lt Return))) (Load Z (UnaryOperation Inc (Store Z (FlowBreak))) ) (Load (Z) Return)

{- Show (Value FlowBreakType) where
  show (FlowBreakValue) = "FlowBreak" -}

fullFuncExample : Instruction [] [] (Nil 0) (Nil 0) (Just Long)
fullFuncExample = (LoadConstant (LongValue 1) $ LoadConstant (LongValue 2) $  (FunctionCall examplefunc  Return ))

e : Value Long
e  = interpret whileExample [0] []

program : Instruction [Text, Long] [] (Just Boolean)
program = LoadConstant (LongValue 10) $
    LoadConstant (LongValue 5) $
    BinaryOperation Add $
    Store (S Z) $ 
    LoadConstant (LongValue 25) $
    BinaryOperation Eq $
    Return

-- Execute the program
result : Value Long
result = interpret program [] []
