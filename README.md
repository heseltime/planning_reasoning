# Projects 1 and 2

For the AI Masters Planning and Reasoning course at JKU.

## 1: Bounded planning encoding in SAT (Sliding Puzzle)

Task: solve sliding puzzle of size 3 × 3. The field contains eight stones numbered with 1 − 8. One field is empty. The stones on the fields left, right, top, or bottom of the empty field can be moved on the empty field. The goal is to sort the stones in ascending order such that the empty field is in the lower right corner. 

Below a possible initial state is shown on the left and the goal state is shown on the right.

<img width="251" alt="image" src="https://github.com/heseltime/planning_reasoning/assets/66922223/e0938964-4f3e-4f46-ad61-9801047c9c4c">

## 2: SMT2 encoding of N-Queens Problem

[SMT2 (Satisfiability Modulo Theories Library 2) Standard](https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf) In this implementation we became especially interested in SMT-Python interfacing, where a system might run fully closed, if z3 executed locally, say, then SMT-code generation -> SMT-evaluation locally, piping to a new (Python) program -> (Python) visualization or some other processing of an SMT-logical result that couldn't be done in Python alone. See diagram of the implementation solution below as well, testing these capabilities.

Task: Solve the N-Queens problem, a classical mathematical problem of placing N queens on an N ×N chessboard such that no two queens are mutually attacking, i.e., no two queens share the same row, column or a diagonal. That is, a solution requires that no two queens share the same row, column, or diagonal. 

The below figure is an example solution for the 4-Queens problem.

<img width="76" alt="image" src="https://github.com/heseltime/planning_reasoning/assets/66922223/221ba85a-35f4-4b2d-8b01-0669de6c1986">

Assumption: N queens on an N by N chessboard.

Approach: We start with the 4 by 4 version of the problem, see 4queens.smt2. From there we generalize the problem (see also NqueensPseudo.smt2). Instead or rote implementation of the 8 by 8 version we try a SMT2-code-generation script in Python, see generate.py - this seems to work when feeding to a [z3 execution web interface](https://jfmc.github.io/z3-play/). The outputs from the interface are contained in and visualized by visualizeXqueensOutput.py with MatPlotLib, reproduced below.

### Results

#### 4x4 (initial hand-coded test, see 4queensTest.smt2):

<img width="382" alt="image" src="https://github.com/heseltime/planning_reasoning/assets/66922223/37ca10b8-2b88-4f8b-b186-ff3bcc796d7a">

Note: This is actually the example solution from the specification.

#### 8x8 (generated, see 8queensGenerated.smt2):


### Diagram

<img width="682" alt="image" src="https://github.com/heseltime/planning_reasoning/assets/66922223/9831652c-bbc6-4ee9-ba04-7eadfdfcdb99">

