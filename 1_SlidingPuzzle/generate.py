import os
import sys

# 2024-01, Planning and Reasoning Project
# Sarah and Jack

# Code to generate the Limboole encoding of the sliding Puzzle problem for a given time steps


if len(sys.argv) < 2:
    sys.exit('Usage: %s <problem size>' % sys.argv[0])

filename = './Puzzle_%sStepsGenerated.boole' % sys.argv[1]
f = open(filename, 'w')

N = int(sys.argv[1])  # ???

print(f'Generate Limboole encoding for {N} steps in {filename}')

f.write('% 2024-01, Planning and Reasoning Project - Generated Code! See generate.py \n')
f.write('% Sarah and Jack\n')
f.write('% see http://fmv.jku.at/limboole for a current (2024-01) web interface to execute\n')

# N = 11  # 11
POSITIONS = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I']
all_moves = []


def encode_state(state, t: str, size=9):
    encoding = []

    # encode where stones are
    for i, stone in enumerate(state):
        encoding.append(f"stone_{stone}_{POSITIONS[i]}_{t} & ")

    # encode where stones are not
    for stone in range(0, size):  # changed 1 to 0 ???
        encoding.append(f"\n")
        for pos in POSITIONS:
            if state[POSITIONS.index(pos)] != stone:
                encoding.append(f"!stone_{stone}_{pos}_{t} & ")

    return ' '.join(encoding)


def mk_mv(time, stone, src, trg):
    global all_moves
    mv_stone_srctrg_time = f"mv_{stone}_{src}{trg}_{time}"
    # add all moves to global list
    all_moves.append(mv_stone_srctrg_time)
    return mv_stone_srctrg_time


def encode_moves(size=9): #try smth in encode moves 1
    encoding = []

    # generating move constraints
    for t in range(N):
        for stone in range(1, size):  # add stone 0 -> encode_moves1
            for idx in range(size):  # 0-8
                encoding.append(f"\n")
                src_pos = POSITIONS[idx]

                # encode all possible moves within puzzle
                if idx % 3 != 2:  # right, if not in rightmost field
                    ###if idx == 0 or idx == 2:
                    trg_pos = POSITIONS[idx + 1]
                    encoding.append(
                        f"({mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & stone_0_{trg_pos}_{t}"
                        f"& !stone_{stone}_{src_pos}_{t + 1} & !stone_0_{trg_pos}_{t + 1} & "  # added !0_t+1 ??? 
                        f"stone_0_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})) & ")  # added & stone_0_{src_pos}_{t+1}

                if idx % 3 != 0:  # left, if not in leftmost field
                    ###if idx == 1 or idx == 3:
                    trg_pos = POSITIONS[idx - 1]
                    encoding.append(
                        f"({mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & stone_0_{trg_pos}_{t}"
                        f"& !stone_{stone}_{src_pos}_{t + 1} & !stone_0_{trg_pos}_{t + 1} & "
                        f"stone_0_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})) & ")  # added & stone_0_{src_pos}_{t+1}
                if idx >= 3:  # move up possible
                    trg_pos = POSITIONS[idx - 3]
                    encoding.append(
                        f"({mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & stone_0_{trg_pos}_{t} "
                        f" & !stone_{stone}_{src_pos}_{t + 1} & !stone_0_{trg_pos}_{t + 1} & "
                        f"stone_0_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})) & ")  # added & stone_0_{src_pos}_{t+1}

                if idx <= 5:  # move down
                    trg_pos = POSITIONS[idx + 3]
                    encoding.append(
                        f"({mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & stone_0_{trg_pos}_{t}"
                        f" & !stone_{stone}_{src_pos}_{t + 1} & !stone_0_{trg_pos}_{t + 1} & "
                        f"stone_0_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})) & ")  # added & stone_0_{src_pos}_{t+1} ???
    return ' '.join(encoding)


def encode_moves1(size=9):
    encoding = []

    # generating move constraints
    for t in range(N):
        for stone in range(1, size):  # add stone 0 -> encode_moves1
            for idx in range(size):  # 0-8
                encoding.append(f"\n")
                src_pos = POSITIONS[idx]

                # encode all possible moves within puzzle
                if idx % 3 != 2:  # right, if not in rightmost field
                    ###if idx == 0 or idx == 2:
                    trg_pos = POSITIONS[idx+1]
                    other_0pos = [i for i in POSITIONS if i != src_pos] # for 0 pos
                    stone0_other_pos = [f"!stone_0_{p}_{t + 1}" for p in other_0pos]
                    stone0_not_pos = ' & '.join(stone0_other_pos)

                    other_trgpos = [i for i in POSITIONS if i != trg_pos]  # for 0 pos
                    stonetrg_other_pos = [f"!stone_{stone}_{p}_{t + 1}" for p in other_trgpos]
                    stonetrg_not_pos = ' & '.join(stonetrg_other_pos)
                    encoding.append(
                        f"({mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & stone_0_{trg_pos}_{t}"
                        f"& {stonetrg_not_pos} & {stone0_not_pos} & "  # added !0_t+1 ??? 
                        f"stone_0_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})) & ")  # added & stone_0_{src_pos}_{t+1}

                if idx % 3 != 0:  # left, if not in leftmost field
                    ###if idx == 1 or idx == 3:
                    trg_pos = POSITIONS[idx - 1]
                    other_pos = [i for i in POSITIONS if i != src_pos]  # for 0 pos
                    stone0_other_pos = [f"!stone_0_{p}_{t + 1}" for p in other_pos]
                    stone0_not_pos = ' & '.join(stone0_other_pos)

                    other_trgpos = [i for i in POSITIONS if i != trg_pos]  # for 0 pos
                    stonetrg_other_pos = [f"!stone_{stone}_{p}_{t + 1}" for p in other_trgpos]
                    stonetrg_not_pos = ' & '.join(stonetrg_other_pos)

                    encoding.append(
                        f"({mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & stone_0_{trg_pos}_{t}"
                        f"& {stonetrg_not_pos} & {stone0_not_pos} & "
                        f"stone_0_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})) & ")  # added & stone_0_{src_pos}_{t+1}
                if idx >= 3:  # move up possible
                    trg_pos = POSITIONS[idx - 3]
                    other_pos = [i for i in POSITIONS if i != src_pos]  # for 0 pos
                    stone0_other_pos = [f"!stone_0_{p}_{t + 1}" for p in other_pos]
                    stone0_not_pos = ' & '.join(stone0_other_pos)

                    other_trgpos = [i for i in POSITIONS if i != trg_pos]  # for 0 pos
                    stonetrg_other_pos = [f"!stone_{stone}_{p}_{t + 1}" for p in other_trgpos]
                    stonetrg_not_pos = ' & '.join(stonetrg_other_pos)

                    encoding.append(
                        f"({mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & stone_0_{trg_pos}_{t} "
                        f" & {stonetrg_not_pos} & {stone0_not_pos} & "
                        f"stone_0_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})) & ")  # added & stone_0_{src_pos}_{t+1}

                if idx <= 5:  # move down
                    trg_pos = POSITIONS[idx + 3]
                    other_pos = [i for i in POSITIONS if i != src_pos]  # for 0 pos
                    stone0_other_pos = [f" !stone_0_{p}_{t + 1}" for p in other_pos]
                    stone0_not_pos = ' & '.join(stone0_other_pos)

                    other_trgpos = [i for i in POSITIONS if i != trg_pos]  # for 0 pos
                    stonetrg_other_pos = [f"!stone_{stone}_{p}_{t + 1}" for p in other_trgpos]
                    stonetrg_not_pos = ' & '.join(stonetrg_other_pos)

                    encoding.append(
                        f"({mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & stone_0_{trg_pos}_{t}"
                        f" & {stonetrg_not_pos} & {stone0_not_pos} & "
                        f"stone_0_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})) & ")  # added & stone_0_{src_pos}_{t+1} ???
    return ' '.join(encoding)


def encode_exact_one_move():
    """
    ToDo: FIX currently 7.8MB - too much
    :return:
    """
    encoding = []
    # encoding.append(f"({' | '.join(all_moves)})") ???
    # at least 1 action at a timestep
    for t in range(N):
        encoding_move_t = []
        for moves in all_moves:
            if moves.endswith(f"_{t}"):
                encoding_move_t.append(moves)
        encoding.append("(" + ' | '.join(encoding_move_t) + ")")
    # at most 1 action - try without ???!
# comment in later ???!!
    for t in range(N):
        moves = [item for item in all_moves if item.endswith(f"_{t}")]
        for i in range(len(moves)):
            for j in range(i + 1, len(moves)):
                encoding.append(f"(!{moves[i]} | !{moves[j]})")

    return ' & '.join(encoding)


def encode_frame_axioms(size=9):
    encoding = []

    for t in range(N):
        for stone in range(0, size):  # change 1 to 0 ???!
            for pos in POSITIONS:
                same_pos = f"stone_{stone}_{pos}_{t} & !stone_{stone}_{pos}_{t + 1}"
                if stone != 0:
                    # diff_pos = [mk_mv(t, stone, pos, other_pos) for other_pos in POSITIONS if other_pos != pos]
                    # the above line generates moves which are just bullshit
                    # get all moves for a certain stone at time t
                    relevant_moves = [move for move in all_moves if f"mv_{stone}_{pos}" in move and f"_{t}" in move]

                    if relevant_moves:
                        moves_per_stone = " | ".join(relevant_moves)
                        encoding.append(f"(({same_pos}) -> ({moves_per_stone}))")

                    # frame axiom for each stone and position
                    # if diff_pos:
                    #   encoding.append(f"(({same_pos}) -> ({' | '.join(diff_pos)}))")
                else:  # added at 16:50 to try out how to handle stone 0 in frame axioms
                    relevant_moves = [move for move in all_moves if f"_{t}" in move]

                    if relevant_moves:
                        moves_per_stone = " | ".join(relevant_moves)
                        encoding.append(f"(({same_pos}) -> ({moves_per_stone}))")

    return ' & \n'.join(encoding)

def encode_frame_axioms2(size=9): # if other pos stone has to have been moved
    encoding = []

    for t in range(N):
        for stone in range(0, size):  # change 1 to 0 ???!
            for pos in POSITIONS:
                same_pos = f"!stone_{stone}_{pos}_{t} & stone_{stone}_{pos}_{t + 1}"
                if stone != 0:
                    # diff_pos = [mk_mv(t, stone, pos, other_pos) for other_pos in POSITIONS if other_pos != pos]
                    # the above line generates moves which are just bullshit
                    # get all moves for a certain stone at time t
                    relevant_moves = [move for move in all_moves if f"mv_{stone}_" in move and f"{pos}_{t}" in move]

                    if relevant_moves:
                        moves_per_stone = " | ".join(relevant_moves)
                        encoding.append(f"(({same_pos}) -> ({moves_per_stone}))")


    return ' & \n'.join(encoding)


def encode_one_stone_one_pos(size=9):  # frame axioms 2
    encoding = []
    # added 11.1. test ???
    for t in range(N):  # N
        for stone in range(0, size):  # change 1 to 0 ???!
            for pos in POSITIONS:
                diff_pos = ""
                curr_pos = f"stone_{stone}_{pos}_{t} "
                other_pos = [other for other in POSITIONS if pos != other]
                for o in other_pos:
                    # if stone == 0: #{stone}
                    diff_pos += f" & !stone_{stone}_{o}_{t}"
                encoding.append(f"{curr_pos}{diff_pos}")

    return ' & \n'.join(encoding)


def encode_one_move_one_time(size=9):  # frame axioms 3 #???
    encoding = []
    # added 11.1. test ???
    for t in range(N):
        for stone in range(1, size):  # change 1 to 0 ???!
            diff_move = ""
            for pos in POSITIONS:
                # same_pos = f"stone_{stone}_{pos}_{t} & !stone_{stone}_{pos}_{t + 1}"
                # diff_pos = [mk_mv(t, stone, pos, other_pos) for other_pos in POSITIONS if other_pos != pos]
                # the above line generates moves which are just bullshit
                # get all moves for a certain stone at time t
                relevant_moves = [move for move in all_moves if f"mv_{stone}_{pos}" in move and f"_{t}" in move]
                for rel_move in relevant_moves[1:]:  # skip 1st
                    diff_move += f" & !{rel_move}"
                encoding.append(f"{relevant_moves[0]}{diff_move}")

    return ' | \n'.join(encoding)


def encode_not_moving_stones(initial_state, goal_state, size=9):
    encoding = []
    # encode where stones are not
    for idx, stone in enumerate(range(1, size)):
        encoding.append(f"\n")
        if initial_state[idx] == goal_state[idx]:
            pos = POSITIONS[idx]
            # add mv action for same pos - don't add those to all_moves since no need to waste time on already correct
            # mv_stone_not = f"mv_{stone}_{pos}{pos}_0"
            encoding.append(f"stone_{stone}_{pos}_{N} & ")
            for p in POSITIONS:
                if p != pos:
                    encoding.append(
                        f"!stone_{stone}_{p}_{N} &")  # f"({mv_stone_not} -> " only add stone add correct pos since no move

    return ' '.join(encoding)


initial_state = [1, 2, 3, 8, 7, 4, 6, 5, 0]  # 12 steps
#initial_state =  [1, 2, 3, 4, 5, 6, 0, 7, 8]  # 2 steps
#initial_state = [1, 2, 3, 0, 5, 6, 4, 7, 8] # 3 steps
f.write('\n %% init state\n')
# stone_1_A_0 & stone_2_B_0 & stone_3_C_0 & stone_8_D_0 & ...
# & !stone_1_B_0 & !stone_1_C_0 & ...
# define where stone can NOT be
encoded_initial_state = encode_state(initial_state, '0')
# print(encoded_initial_state)
f.write(encoded_initial_state)

goal_state = [1, 2, 3, 4, 5, 6, 7, 8, 0]

f.write('\n %% goal state\n')
# stone_1_A_n & stone_2_B_n & stone_3_C_n & stone_4_D_n & ...
# & !stone_2_A_n & !stone_2_C_n & !stone_2_D_n & ...
# define where stone can NOT be - XOR not necessary since only 1 Goal state!
encoded_goal_state = encode_state(goal_state, str(N))
f.write(encoded_goal_state)

f.write('\n')  # ???
encoded_not_moving = encode_not_moving_stones(initial_state, goal_state)  # print to frame axioms???
f.write('\n % stones with correct position from beginning\n')
f.write(encoded_not_moving)

# execute actions
f.write('\n %% actions\n')
f.write('\n')  # ???
# mv_5_HI_0 -> ((stone_5_H_0 & !stone_5_I_0 ..?) & (!stone_5_H_1 & stone_5_I_1)) #rest pos NOT?
# do for every timeste
encoded_moves = encode_moves1() #1???
# print(encoded_moves)
f.write(encoded_moves)

# exactly 1 action
f.write('\n %% exactly 1 action\n')
f.write('\n')  # ???
# (mv_5_HI_0 | mv_6_GH_0 | ...) & (!mv_5_HI_0 | !mv_6_GH_0 | !...)
encoded_one_move = encode_exact_one_move()
# print(encoded_one_move[:1000])
f.write(encoded_one_move)  # if not printed - 333kB, otherwise 9.6MB ???
# possible reduction by checking where the initial state is and moving from there

# frame axioms
f.write('\n %% frame axioms\n')
f.write(' & \n')  # ???
# ((stone_5_H_0 & !stone_5_H_1) -> mv_5_HI_0) &...
encoded_frame_axioms = encode_frame_axioms()
# print(encoded_frame_axioms)
f.write(encoded_frame_axioms)

f.write('\n %% frame axioms 2\n')
f.write(' & \n')  # ???
# ((stone_5_H_0 & !stone_5_H_1) -> mv_5_HI_0) &...
encoded_frame_axioms2 = encode_frame_axioms2()
# print(encoded_frame_axioms)
f.write(encoded_frame_axioms2)

#f.write('\n %% stone 0 not at 2 different position at same time\n')
#encoded_frame_ax = encode_one_stone_one_pos()
#f.write(' & \n')
#f.write(encoded_frame_ax)

#f.write('\n %% move action not at 2 different position at same time\n')
# encoded_frame_ax2 = encode_one_move_one_time()
# f.write(' & \n')
# f.write(encoded_frame_ax2)

# Limboole http://fmv.jku.at/limboole


# If number of steps guessed too high -> formula unsat
# if too low also unsat - how to handle that?