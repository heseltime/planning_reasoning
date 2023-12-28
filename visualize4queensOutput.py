import matplotlib.pyplot as plt
import matplotlib.image as mpimg
import numpy as np

# 2023-12, Planning and Reasoning Project
# Sarah and Jack

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
    (define-fun x0y3 () Bool false)
    (define-fun x0y1 () Bool false)
    (define-fun x2y3 () Bool true)
    (define-fun x2y0 () Bool false)
    (define-fun x1y2 () Bool false)
    (define-fun x3y0 () Bool true)
    (define-fun x3y3 () Bool false)
    (define-fun x0y2 () Bool true)
    (define-fun x1y3 () Bool false)
    (define-fun x2y1 () Bool false)
    (define-fun x2y2 () Bool false)
    (define-fun x1y1 () Bool true)
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
