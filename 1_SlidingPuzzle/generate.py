import os
import sys

# 2024-01, Planning and Reasoning Project
# Sarah and Jack

# Code to generate the Limboole encoding of the sliding Puzzle problem for a given time steps


if len(sys.argv) < 2:
    sys.exit('Usage: %s <problem size>' % sys.argv[0]) #???

filename = '1_SlidingPuzzle/Puzzle_%sStepsGenerated.boole' % sys.argv[1]
f = open(filename, 'w')

N = int(sys.argv[1]) #???

print(f'Generate Limboole encoding for {N} steps in {filename}')

f.write('% 2024-01, Planning and Reasoning Project - Generated Code! See generate.py \n')
f.write('% Sarah and Jack\n')
f.write('% see http://fmv.jku.at/limboole for a current (2024-01) web interface to execute\n')

#N = 11  # 11
POSITIONS = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I']
all_moves = []


def encode_state(state, t: str):
    encoding = []

    # encode where stones are
    for i, stone in enumerate(state):
        # How to handly empty stone = 0???
        encoding.append(f"stone_{stone}_{POSITIONS[i]}_{t}")

    # encode where stones are not
    for stone in range(1, 9):
        encoding.append(f"\n")
        for pos in POSITIONS:
            if initial_state[POSITIONS.index(pos)] != stone:
                encoding.append(f"!stone_{stone}_{pos}_{t}")

    return ' & '.join(encoding)


def gen_moves(time, field, src, trg):
    return f'mv_{time}_{field}_{src}{trg}'
    # generate move variable names


def mk_mv(time, stone, src, trg):  # global list???
    global all_moves
    mv_stone_srctrg_time = f"mv_{stone}_{src}{trg}_{time}"
    # add all moves to global list
    all_moves.append(mv_stone_srctrg_time)
    return mv_stone_srctrg_time


def encode_moves():
    encoding = []

    # generating move constraints
    for t in range(N):
        for stone in range(1, 9):
            for idx in range(9):  # 0-8
                encoding.append(f"\n")
                src_pos = POSITIONS[idx]

                # encode all possible moves within puzzle
                if idx % 3 != 2:  # right, if not in rightmost field
                    trg_pos = POSITIONS[idx + 1]
                    encoding.append(f"{mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & "
                                    f"!stone_{stone}_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})")
                if idx % 3 != 0:  # left, if not in leftmost field
                    trg_pos = POSITIONS[idx - 1]
                    encoding.append(f"{mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & "
                                    f"!stone_{stone}_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})")
                if idx >= 3:  # move up possible
                    trg_pos = POSITIONS[idx - 3]
                    encoding.append(f"{mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & "
                                    f"!stone_{stone}_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})")
                if idx <= 5:  # move down
                    trg_pos = POSITIONS[idx + 3]
                    encoding.append(f"{mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & "
                                    f"!stone_{stone}_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})")

    return ' & '.join(encoding)


def encode_exact_one_move():
    encoding = []

    for t in range(N):

        # at least one move
        encoding.append(f"({' | '.join(all_moves)})")

        # at most one move
        for i in range(len(all_moves)):
            for j in range(i + 1, len(all_moves)):
                encoding.append(f"!({all_moves[i]} & {all_moves[j]})")

    return ' & '.join(encoding)


def encode_frame_axioms():
    encoding = []

    for t in range(N-1):  # not needed for last step ???
        for stone in range(1, 9):
            for pos in POSITIONS:
                same_pos = f"stone_{stone}_{pos}_{t} & !stone_{stone}_{pos}_{t + 1}"

                diff_pos = [mk_mv(t, stone, pos, other_pos) for other_pos in POSITIONS if other_pos != pos]

                # frame axiom for each stone and position
                if diff_pos:
                    encoding.append(f"(({same_pos}) -> ({' | '.join(diff_pos)}))")

    return ' & \n'.join(encoding)


initial_state = [1, 2, 3, 8, 7, 4, 6, 5, 0]
f.write('%% init state\n')
# stone_1_A_0 & stone_2_B_0 & stone_3_C_0 & stone_8_D_0 & ...
# & !stone_1_B_0 & !stone_1_C_0 & ...
# define where stone can NOT be

encoded_initial_state = encode_state(initial_state, '0')
# print(encoded_initial_state)
f.write(encoded_initial_state)
f.write('\n')

goal_state = [1, 2, 3, 4, 5, 6, 7, 8, 0]
f.write('%% goal state\n')
# stone_1_A_n & stone_2_B_n & stone_3_C_n & stone_4_D_n & ...
# & !stone_2_A_n & !stone_2_C_n & !stone_2_D_n & ...
# define where stone can NOT be - XOR not necessary since only 1 Goal state!
encoded_goal_state = encode_state(goal_state, str(N))
f.write(encoded_goal_state)
f.write('\n')

# execute actions
f.write('%% actions\n')
# mv_5_HI_0 -> ((stone_5_H_0 & !stone_5_I_0 ..?) & (!stone_5_H_1 & stone_5_I_1)) #rest pos NOT?
# do for every timeste
encoded_moves = encode_moves()
#print(encoded_moves)
f.write(encoded_moves)
f.write('\n')

# exactly 1 action
f.write('%% exactly 1 action\n')
# (mv_5_HI_0 | mv_6_GH_0 | ...) & (!mv_5_HI_0 | !mv_6_GH_0 | !...)
encoded_one_move = encode_exact_one_move()
# print(encoded_one_move[:1000])
f.write(encoded_one_move)
f.write('\n')


# frame axioms
f.write('%% frame axioms\n')
# ((stone_5_H_0 & !stone_5_H_1) -> mv_5_HI_0) &...
encoded_frame_axioms = encode_frame_axioms()
#print(encoded_frame_axioms)
f.write(encoded_frame_axioms)

# Limboole http://fmv.jku.at/limboole
