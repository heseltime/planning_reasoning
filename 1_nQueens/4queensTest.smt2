; 2023-12, Planning and Reasoning Project
; Sarah and Jack
;
; N-queens problem for the 4x4 case to start, see comments above code blocks for approach (SMT2)
;
; see https://jfmc.github.io/z3-play/ for a current (2023-12) z3 web interface to execute

; playing field
(declare-const x0y0 Bool)
(declare-const x0y1 Bool)
(declare-const x0y2 Bool)
(declare-const x0y3 Bool)
(declare-const x1y0 Bool)
(declare-const x1y1 Bool)
(declare-const x1y2 Bool)
(declare-const x1y3 Bool)
(declare-const x2y0 Bool)
(declare-const x2y1 Bool)
(declare-const x2y2 Bool)
(declare-const x2y3 Bool)
(declare-const x3y0 Bool)
(declare-const x3y1 Bool)
(declare-const x3y2 Bool)
(declare-const x3y3 Bool)

; 4 queens on the field, one per row
(assert (or x0y0  x0y1  x0y2 x0y3))
(assert (or x1y0  x1y1  x1y2 x1y3))
(assert (or x2y0  x2y1  x2y2 x2y3))
(assert (or x3y0  x3y1  x3y2 x3y3))

; 2 queens should never be on the same line ...
(assert (not (or (and x0y1 x0y0) (and x0y2 x0y0) (and x0y2 x0y1) (and x0y3 x0y0) (and x0y3 x0y1) (and x0y3 x0y2))))
(assert (not (or (and x1y1 x1y0) (and x1y2 x1y0) (and x1y2 x1y1) (and x1y3 x1y0) (and x1y3 x1y1) (and x1y3 x1y2))))
(assert (not (or (and x2y1 x2y0) (and x2y2 x2y0) (and x2y2 x2y1) (and x2y3 x2y0) (and x2y3 x2y1) (and x2y3 x2y2))))
(assert (not (or (and x3y1 x3y0) (and x3y2 x3y0) (and x3y2 x3y1) (and x3y3 x3y0) (and x3y3 x3y1) (and x3y3 x3y2))))

; ... or column ...
(assert (not (or (and x1y0 x0y0) (and x2y0 x0y0) (and x2y0 x1y0) (and x3y0 x0y0) (and x3y0 x1y0) (and x3y0 x2y0))))
(assert (not (or (and x1y1 x0y1) (and x2y1 x0y1) (and x2y1 x1y1) (and x3y1 x0y1) (and x3y1 x1y1) (and x3y1 x2y1))))
(assert (not (or (and x1y2 x0y2) (and x2y2 x0y2) (and x2y2 x1y2) (and x3y2 x0y2) (and x3y2 x1y2) (and x3y2 x2y2))))
(assert (not (or (and x1y3 x0y3) (and x2y3 x0y3) (and x2y3 x1y3) (and x3y3 x0y3) (and x3y3 x1y3) (and x3y3 x2y3))))

; ... or diagonal: both directions! We start with the main, four-field diagonals
(assert (not (or (and x0y0 x1y1) (and x0y0 x2y2) (and x0y0 x3y3) (and x1y1 x2y2) (and x1y1 x3y3) (and x2y2 x3y3))))
(assert (not (or (and x1y1 x0y0) (and x2y2 x0y0) (and x3y3 x0y0) (and x2y2 x1y1) (and x3y3 x1y1) (and x3y3 x2y2))))
; continued! But rotate 90 degrees
(assert (not (or (and x3y0 x2y1) (and x3y0 x1y2) (and x3y0 x0y3) (and x2y1 x1y2) (and x2y1 x0y3) (and x1y2 x0y3))))
(assert (not (or (and x2y1 x3y0) (and x1y2 x3y0) (and x0y3 x3y0) (and x1y2 x2y1) (and x0y3 x2y1) (and x0y3 x1y2)))) ; again second directions

; three-field diags
(assert (not (or (and x0y1 x1y2) (and x0y1 x2y3) (and x1y2 x2y3)))) ; top left-ish (first quadrant)
(assert (not (or (and x1y2 x0y1) (and x2y3 x0y1) (and x2y3 x1y2)))) 
(assert (not (or (and x1y0 x2y1) (and x1y0 x3y2) (and x2y1 x3y2)))) ; bottom right-ish
(assert (not (or (and x2y1 x1y0) (and x3y2 x1y0) (and x3y2 x2y1))))
; continued! But rotate 90 degrees
(assert (not (or (and x3y1 x2y2) (and x3y1 x1y3) (and x2y2 x1y3)))) ; top right-ish
(assert (not (or (and x2y2 x3y1) (and x1y3 x3y1) (and x1y3 x2y2)))) 
(assert (not (or (and x0y2 x1y1) (and x1y1 x2y0) (and x0y2 x2y0)))) ; bottom left-ish
(assert (not (or (and x1y1 x0y2) (and x2y0 x1y1) (and x2y0 x0y2))))

; two-field diags
(assert (not (or (and x0y2 x1y3)))) ; top left
(assert (not (or (and x1y3 x0y2))))
(assert (not (or (and x2y0 x3y1)))) ; bottom right
(assert (not (or (and x3y1 x2y0))))
; continued! But rotate 90 degrees
(assert (not (or (and x2y3 x3y2)))) ; top right
(assert (not (or (and x3y2 x2y3))))
(assert (not (or (and x0y2 x1y3)))) ; bottom left
(assert (not (or (and x1y3 x0y2))))

; finally, check if the model is satisfiable and output a model
(check-sat)
(get-model)