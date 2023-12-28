import matplotlib.pyplot as plt
import matplotlib.image as mpimg
import numpy as np

# 2023-12, Planning and Reasoning Project
# Sarah and Jack

# quick visualization of the N-Queens problem,
# based on the output of the Z3 solver for a given n

# TO USE: SPECIFY N ...
n = 8

# ... AND SMT2 OUTPUT from Z3 solver
smt2_output = """
  (define-fun x1y6 () Bool true)
  (define-fun x1y0 () Bool false)
  (define-fun x3y2 () Bool false)
  (define-fun x6y4 () Bool false)
  (define-fun x6y7 () Bool false)
  (define-fun x0y5 () Bool false)
  (define-fun x6y2 () Bool false)
  (define-fun x6y3 () Bool false)
  (define-fun x1y5 () Bool false)
  (define-fun x7y5 () Bool false)
  (define-fun x3y6 () Bool false)
  (define-fun x4y1 () Bool false)
  (define-fun x1y3 () Bool false)
  (define-fun x1y4 () Bool false)
  (define-fun x7y7 () Bool false)
  (define-fun x2y2 () Bool false)
  (define-fun x5y0 () Bool false)
  (define-fun x3y1 () Bool false)
  (define-fun x0y6 () Bool false)
  (define-fun x7y6 () Bool false)
  (define-fun x0y3 () Bool false)
  (define-fun x1y7 () Bool false)
  (define-fun x6y6 () Bool false)
  (define-fun x2y0 () Bool false)
  (define-fun x0y4 () Bool false)
  (define-fun x5y2 () Bool true)
  (define-fun x3y0 () Bool false)
  (define-fun x2y5 () Bool true)
  (define-fun x5y1 () Bool false)
  (define-fun x0y2 () Bool false)
  (define-fun x6y0 () Bool false)
  (define-fun x7y4 () Bool false)
  (define-fun x5y5 () Bool false)
  (define-fun x1y1 () Bool false)
  (define-fun x2y7 () Bool false)
  (define-fun x6y1 () Bool true)
  (define-fun x4y5 () Bool false)
  (define-fun x5y4 () Bool false)
  (define-fun x0y1 () Bool false)
  (define-fun x7y1 () Bool false)
  (define-fun x5y7 () Bool false)
  (define-fun x1y2 () Bool false)
  (define-fun x3y3 () Bool false)
  (define-fun x4y3 () Bool true)
  (define-fun x6y5 () Bool false)
  (define-fun x3y5 () Bool false)
  (define-fun x2y1 () Bool false)
  (define-fun x0y0 () Bool false)
  (define-fun x4y2 () Bool false)
  (define-fun x0y7 () Bool true)
  (define-fun x2y4 () Bool false)
  (define-fun x7y2 () Bool false)
  (define-fun x2y3 () Bool false)
  (define-fun x4y4 () Bool false)
  (define-fun x4y6 () Bool false)
  (define-fun x7y0 () Bool true)
  (define-fun x5y6 () Bool false)
  (define-fun x4y0 () Bool false)
  (define-fun x3y7 () Bool false)
  (define-fun x5y3 () Bool false)
  (define-fun x4y7 () Bool false)
  (define-fun x3y4 () Bool true)
  (define-fun x2y6 () Bool false)
  (define-fun x7y3 () Bool false)
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
            #print(position)
            x, y = int(position[1]), int(position[3])
            board[y, x] = 1


plt.figure(figsize=(n + 2, n + 2))
plt.xticks(range(n))
plt.yticks(range(n))
plt.title(str(n) + 'x' + str(n) + ' N-Queens Problem')


# checkered pattern for the board
for y in range(n):
    for x in range(n):
        if (x + y) % 2 == 0:
            plt.fill_between([x, x + 1], [y, y], [y + 1, y + 1], color='gray', alpha=0.5)

# Place crown images instead of 'Q'
for y in range(n):
    for x in range(n):
        if board[y, x] == 1:
            plt.fill_between([x, x + 1], [y, y], [y + 1, y + 1], color='black', alpha=1)
            #plt.imshow(mpimg.imread('crown64.jpg'), extent=[x, x + 1, y, y + 1])
            plt.text(x + 0.5, y + 0.5, 'Q', fontsize=12, ha='center', va='center', color='white')

plt.show()
