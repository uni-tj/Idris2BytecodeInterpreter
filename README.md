# Idris 2 Intrinscally-Typed-Interpreter
## Overview

This Idris2 project provides a bytecode interpreter that leverages dependent types to enforce the construction of well-formed programs. This design ensures program correctness and offers a robust foundation for safe and reliable execution.

## Key Features

- Dependent Typing: Ensures that only valid programs can be represented within the interpreter, preventing runtime errors due to incorrect program structure.
  Instruction Set: Includes a comprehensive set of instructions to perform arithmetic, logical, memory-related, and control flow operations:
- Arithmetic: LoadConstant, BinaryOperation (Add, Sub, Mul, etc.), UnaryOperation (Inc, Dec, etc.)
  Variables: Store, Load,
- Heap(experimental on feature/heap ) Allocate // The Heap is currently experiencing a bug and is not working!
- Control Flow: Jump, CondJump, If, While, Return
- FunctionCalls: This Interpreter allows calling Functions that are provided through the Func DataType  
- Value Types: Supports a variety of data types:
  - Text
  - Long
  - Float
  - Boolean
- Example Programs: Includes examples demonstrating how to construct and execute programs using the interpreter.
- [ Heap: Provides a heap model (Hp module) for dynamic memory management. ] // on the ``` feature/heap``` branch

## Getting Started
To use the Interpret function can be used by providing a Programm and a list of Locals and a Stack. 
```
-- Define a simple program
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
```

