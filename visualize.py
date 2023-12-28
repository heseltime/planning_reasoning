import matplotlib.pyplot as plt
import numpy as np

# 2023-12, Planning and Reasoning Project
# quick visualization of the N-Queens problem,
# based on the output of the Z3 solver for a given n

# TO USE: SPECIFY N ...
n = 4

# ... AND SMT2 OUTPUT from Z3 solver
smt2_output = """
  (define-fun x3y1 () Bool false)
  (define-fun x0y0 () Bool false)
  (define-fun x3y2 () Bool false)
  (define-fun x1y0 () Bool false)
  (define-fun x0y3 () Bool true)
  (define-fun x0y1 () Bool false)
  (define-fun x2y3 () Bool false)
  (define-fun x2y0 () Bool false)
  (define-fun x1y2 () Bool true)
  (define-fun x3y0 () Bool true)
  (define-fun x3y3 () Bool false)
  (define-fun x0y2 () Bool false)
  (define-fun x1y3 () Bool false)
  (define-fun x2y1 () Bool true)
  (define-fun x2y2 () Bool false)
  (define-fun x1y1 () Bool false)
"""

####################
# DO NOT EDIT BELOW #
####################

# parse the output to extract queen positions to board representation
board = np.zeros((n, n), dtype=int)
for line in smt2_output.splitlines():
    if "define-fun" in line:
        parts = line.split()
        position = parts[1]
        value = parts[-1][:-1] # trim the trailing bracket
        if value == "true":
            x, y = int(position[1]), int(position[3])
            board[y, x] = 1

# create a chess board visualization
plt.figure(figsize=(n + 2, n + 2))
plt.imshow(board, cmap='gray_r')
plt.xticks(range(n))
plt.yticks(range(n))
plt.title('4x4 N-Queens Problem')

# Mark the queens
for y in range(n):
    for x in range(n):
        if board[y, x] == 1:
            plt.text(x, y, 'Q', fontsize=10, ha='center', va='center', color='white')

plt.show()
