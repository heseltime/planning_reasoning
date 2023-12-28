; 2023-12, Planning and Reasoning Project
; Sapce and Jack
;
; N-queens problem high-level/pseudo, to be implemented in 4x4 and 8x8

; Comment: Implementing this in a specific SMT-LIB compatible solver would require 
; writing a script (in Python or another language) that generates these constraints 
; based on the given N. This script would then output the generated SMT-LIB code, 
; which can be fed into the solver to find a solution.

; assume N is defined, declare the playing field
(declare-const q[0..N-1][0..N-1] Bool)

; one queen per row
(for i in 0..N-1):
    (assert (or q[i][0] q[i][1] ... q[i][N-1]))

; one queen per column
(for j in 0..N-1):
    (assert (or q[0][j] q[1][j] ... q[N-1][j]))

; diagonal constraints
(for each cell q[i][j]):
    ; check all other cells q[k][l] where k != i and l != j
    ; add constraints to ensure they are not on the same diagonal

(check-sat)
(get-model)
