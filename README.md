# Projects 1 and 2

For the AI Masters Planning and Reasoning course at JKU.

## 1: Bounded planning encoding in SAT (Sliding Puzzle)

Task: solve sliding puzzle of size 3 × 3. The field contains eight stones numbered with 1 − 8. One field is empty. The stones on the fields left, right, top, or bottom of the empty field can be moved on the empty field. The goal is to sort the stones in ascending order such that the empty field is in the lower right corner.
Below a possible initial state is shown on the left and the goal state is shown on the right.

<img width="251" alt="image" src="https://github.com/heseltime/planning_reasoning/assets/66922223/e0938964-4f3e-4f46-ad61-9801047c9c4c">

Assumption: Number of steps to solve the puzzle is known

Approach: First we encoded a simple sliding puzzle, where only 2 steps need to be taken to end up in the required 
goal state. The encoding is structured the same way as proposed in the lecture. The text file starts with by an
encoding for the initial state and the goal state, followed by a definition of "move"-actions and its constraints of executing 
exactly one action at a time and finished with the encoding of the frame axioms. For a detailed explanation we refer to 
the .boole files or to the 1_SlidingPuzzle/generate.py for the implementation.

[Limboole (SAT Solver)](https://fmv.jku.at/limboole/)

### Results
For the evaluation we downloaded Limboole for Windows and used the command-line interpreter. 
An example of which inputs to use, until to obtain the result of the puzzle: <br>
Starting from our project folder <br>
```python 1_SlidingPuzzle/generate.py 2 ``` <br>
```limboole -s Puzzle_2StepsGenerated.boole > encoding_output2.txt ``` <br>
```findstr /c:"= 1" encoding_output2.txt | findstr "mv" ``` <br>
Result: <br>
mv_7_HG_0 = 1 <br>
mv_8_IH_1 = 1

As seen above with the command ```findstr``` it's possible to filter out the interesting variables or assignments.

#### 2 Steps (see Puzzle_2StepsGenerated.boole, encoding_output2.txt)
With the initial state = [1, 2, 3, 4, 5, 6, 0, 7, 8] we need 2 steps to end up in the goal state = [1, 2, 3, 4, 5, 6, 7, 8, 0]. 
For this set up, stones 7 and 8 have to be moved to the right and the empty stone accordingly to the left.
The encoding can can be found in Puzzle_2StepsGenerated.boole.

#### 12 Steps (see Puzzle_12StepsGenerated.boole, encoding_output12.txt)
With the initial state = [1, 2, 3, 8, 7, 4, 6, 5, 0]  we need 12 steps to end up in the goal state = [1, 2, 3, 4, 5, 6, 7, 8, 0]. 
The encoding for this proposed initial state can be found in the 7.5MB large text file Puzzle_12StepsGenerated.boole. The most
interesting part are most likely the truth values for the actions:
```findstr /c:"= 1" encoding_output12.txt | findstr "mv"``` <br>
mv_5_HI_0 = 1 <br>
mv_6_GH_1 = 1 <br>
mv_8_DG_2 = 1 <br>
mv_7_ED_3 = 1 <br>
mv_4_FE_4 = 1 <br>
mv_5_IF_5 = 1 <br>
mv_6_HI_6 = 1 <br>
mv_8_GH_7 = 1<br>
mv_7_DG_8 = 1<br>
mv_4_ED_9 = 1<br>
mv_5_FE_10 = 1<br>
mv_6_IF_11 = 1<br>

By manually checking we could confirm that this path is indeed correct.

## 2: SMT2 encoding of N-Queens Problem

[SMT2 (Satisfiability Modulo Theories Library 2) Standard](https://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2021-05-12.pdf) In this implementation we became especially interested in SMT-Python interfacing, where a system might run fully closed, if z3 executed locally, say, then SMT-code generation -> SMT-evaluation locally, piping to a new (Python) program -> (Python) visualization or some other processing of an SMT-logical result that couldn't be done in Python alone. See diagram of the implementation solution below as well, testing these capabilities.

Task: Solve the N-Queens problem, a classical mathematical problem of placing N queens on an N ×N chessboard such that no two queens are mutually attacking, i.e., no two queens share the same row, column or a diagonal. That is, a solution requires that no two queens share the same row, column, or diagonal. 

The below figure is an example solution for the 4-Queens problem.

<img width="76" alt="image" src="https://github.com/heseltime/planning_reasoning/assets/66922223/221ba85a-35f4-4b2d-8b01-0669de6c1986">

Assumption: N queens on an N by N chessboard.

Approach: We start with the 4 by 4 version of the problem, see 4queens.smt2. From there we generalize the problem (see also NqueensPseudo.smt2). Instead or rote implementation of the 8 by 8 version we try a SMT2-code-generation script in Python, see generate.py - this seems to work when feeding to a [z3 execution web interface](https://jfmc.github.io/z3-play/). The outputs from the interface are contained in and visualized by visualizeXqueensOutput.py with MatPlotLib, reproduced below.

### Results

#### 4x4 (initial hand-coded test, see 4queensTest.smt2)

<img width="382" alt="image" src="https://github.com/heseltime/planning_reasoning/assets/66922223/37ca10b8-2b88-4f8b-b186-ff3bcc796d7a">

Note: This is actually the example solution from the specification, depicted above.

#### 8x8 (generated, see 8queensGenerated.smt2)

<img width="603" alt="image" src="https://github.com/heseltime/planning_reasoning/assets/66922223/cee076a1-7329-466e-b167-97b79775c65a">

**This also represents to the Project solution to Problem 1, together with the SMT2-generator script, generate.py, all in folder 2_nQueens of the repo.**

### Diagram Overview of Project 2

<img width="692" alt="image" src="https://github.com/heseltime/planning_reasoning/assets/66922223/1bd792d6-5e80-48b5-95f3-854d5f21dfcd">


### Further Note

Since the solution for the 8x8 problem is generically generated, it can be applied to even larger scale versions of the N-queens problem, e.g. 16- and 32-queens, although the 32-queens problem's SMT encoding did not execute on the reference z3 tool anymore ([z3 Playground](https://jfmc.github.io/z3-play/)). 


