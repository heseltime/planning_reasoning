import sys

# 2024-01, Planning and Reasoning Project
# Sarah and Jack

# Code to generate the Limboole encoding of the sliding Puzzle problem for given N time steps

if len(sys.argv) < 2:
    sys.exit('Usage: %s <problem size>' % sys.argv[0])

filename = './Puzzle_%sStepsGenerated.boole' % sys.argv[1]
f = open(filename, 'w')

N = int(sys.argv[1])  # global variable to define the number of steps needed

print(f'Generating Limboole encoding for {N} steps in {filename}')

f.write('% 2024-01, Planning and Reasoning Project - Generated Code! See generate.py \n')
f.write('% Sarah and Jack\n')
f.write('% see http://fmv.jku.at/limboole for a current (2024-01) web interface to execute\n')

POSITIONS = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I']
all_moves = []


def encode_state(state, t: str, size=9):
    encoding = []

    # encode where stones are
    for i, stone in enumerate(state):
        encoding.append(f"stone_{stone}_{POSITIONS[i]}_{t} & ")

    # encode where stones are not
    for stone in range(0, size):
        encoding.append(f"\n")
        for pos in POSITIONS:
            if state[POSITIONS.index(pos)] != stone:
                encoding.append(f"!stone_{stone}_{pos}_{t} & ")

    return ' '.join(encoding)


def mk_mv(time, stone, src, trg):
    global all_moves
    # generate move actions
    mv_stone_srctrg_time = f"mv_{stone}_{src}{trg}_{time}"
    # add all moves to global list
    all_moves.append(mv_stone_srctrg_time)
    return mv_stone_srctrg_time


def encode_moves(size=9):
    encoding = []

    # generating move constraints
    for t in range(N):
        # skip stone 0, we only encode moves for all other stones and add actions for 0 during this movement
        for stone in range(1, size):
            for idx in range(size):  # 0-8
                encoding.append(f"\n")
                src_pos = POSITIONS[idx]
                # save all positions except the src
                other_0pos = [i for i in POSITIONS if i != src_pos]
                # since the src is going to be stone 0 at that position all others are negated at that next timestep
                stone0_other_pos = [f"!stone_0_{p}_{t + 1}" for p in other_0pos]
                stone0_not_pos = ' & '.join(stone0_other_pos)

                # encode all possible moves within puzzle
                if idx % 3 != 2:  # right, if not in rightmost field
                    trg_pos = POSITIONS[idx + 1]

                    # save all pos except target
                    other_trgpos = [i for i in POSITIONS if i != trg_pos]
                    # since the trg is going to be the current stone at that position all others are negated at
                    # the next timestep
                    stonetrg_other_pos = [f"!stone_{stone}_{p}_{t + 1}" for p in other_trgpos]
                    stonetrg_not_pos = ' & '.join(stonetrg_other_pos)

                    encoding.append(
                        f"({mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & stone_0_{trg_pos}_{t}"
                        f"& {stonetrg_not_pos} & {stone0_not_pos} & "  
                        f"stone_0_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})) & ")

                if idx % 3 != 0:  # left, if not in leftmost field
                    trg_pos = POSITIONS[idx - 1]
                    #other_pos = [i for i in POSITIONS if i != src_pos]  # for 0 pos
                    #stone0_other_pos = [f"!stone_0_{p}_{t + 1}" for p in other_pos]
                    #stone0_not_pos = ' & '.join(stone0_other_pos)

                    other_trgpos = [i for i in POSITIONS if i != trg_pos]
                    # since the trg is going to be the current stone at that position all others are negated at
                    # the next timestep
                    stonetrg_other_pos = [f"!stone_{stone}_{p}_{t + 1}" for p in other_trgpos]
                    stonetrg_not_pos = ' & '.join(stonetrg_other_pos)

                    encoding.append(
                        f"({mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & stone_0_{trg_pos}_{t}"
                        f"& {stonetrg_not_pos} & {stone0_not_pos} & "
                        f"stone_0_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})) & ")
                if idx >= 3:  # move up possible
                    trg_pos = POSITIONS[idx - 3]
                    #other_pos = [i for i in POSITIONS if i != src_pos]  # for 0 pos
                    #stone0_other_pos = [f"!stone_0_{p}_{t + 1}" for p in other_pos]
                    #stone0_not_pos = ' & '.join(stone0_other_pos)

                    other_trgpos = [i for i in POSITIONS if i != trg_pos]
                    # since the trg is going to be the current stone at that position all others are negated at
                    # the next timestep
                    stonetrg_other_pos = [f"!stone_{stone}_{p}_{t + 1}" for p in other_trgpos]
                    stonetrg_not_pos = ' & '.join(stonetrg_other_pos)

                    encoding.append(
                        f"({mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & stone_0_{trg_pos}_{t} "
                        f" & {stonetrg_not_pos} & {stone0_not_pos} & "
                        f"stone_0_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})) & ")

                if idx <= 5:  # move down
                    trg_pos = POSITIONS[idx + 3]
                   # other_pos = [i for i in POSITIONS if i != src_pos]  # for 0 pos
                   # stone0_other_pos = [f" !stone_0_{p}_{t + 1}" for p in other_pos]
                   # stone0_not_pos = ' & '.join(stone0_other_pos)

                    other_trgpos = [i for i in POSITIONS if i != trg_pos]
                    # since the trg is going to be the current stone at that position all others are negated at
                    # the next timestep
                    stonetrg_other_pos = [f"!stone_{stone}_{p}_{t + 1}" for p in other_trgpos]
                    stonetrg_not_pos = ' & '.join(stonetrg_other_pos)

                    encoding.append(
                        f"({mk_mv(t, stone, src_pos, trg_pos)} -> (stone_{stone}_{src_pos}_{t} & stone_0_{trg_pos}_{t}"
                        f" & {stonetrg_not_pos} & {stone0_not_pos} & "
                        f"stone_0_{src_pos}_{t + 1} & stone_{stone}_{trg_pos}_{t + 1})) & ")
    return ' '.join(encoding)


def encode_exact_one_move():
    encoding = []
    # at least 1 action at a timestep
    for t in range(N):
        encoding_move_t = []
        for moves in all_moves:
            if moves.endswith(f"_{t}"):
                encoding_move_t.append(moves)
        encoding.append("(" + ' | '.join(encoding_move_t) + ")")

    # at most 1 action - contributes most to te size of the file, since we have to generate all possible pairs of moves
    for t in range(N):
        moves = [item for item in all_moves if item.endswith(f"_{t}")]
        for i in range(len(moves)):
            for j in range(i + 1, len(moves)):
                encoding.append(f"(!{moves[i]} | !{moves[j]})")

    return ' & '.join(encoding)


def encode_frame_axioms(size=9):
    # if a stone changed its position from one to another time step, an action was executed
    encoding = []

    for t in range(N):
        for stone in range(0, size):
            for pos in POSITIONS:
                same_pos = f"stone_{stone}_{pos}_{t} & !stone_{stone}_{pos}_{t + 1}"
                if stone != 0:
                    # get all moves for a certain stone at time t
                    relevant_moves = [move for move in all_moves if f"mv_{stone}_{pos}" in move and f"_{t}" in move]

                    if relevant_moves:
                        moves_per_stone = " | ".join(relevant_moves)
                        encoding.append(f"(({same_pos}) -> ({moves_per_stone}))")

                else:
                    relevant_moves = [move for move in all_moves if f"_{t}" in move]

                    if relevant_moves:
                        moves_per_stone = " | ".join(relevant_moves)
                        encoding.append(f"(({same_pos}) -> ({moves_per_stone}))")

    return ' & \n'.join(encoding)


def encode_frame_axioms2(size=9):
    # if the stone has been moved to another position stone has to have moved
    encoding = []

    for t in range(N):
        for stone in range(0, size):
            for pos in POSITIONS:
                same_pos = f"!stone_{stone}_{pos}_{t} & stone_{stone}_{pos}_{t + 1}"
                if stone != 0:
                    # get all moves for a certain stone at time t
                    relevant_moves = [move for move in all_moves if f"mv_{stone}_" in move and f"{pos}_{t}" in move]

                    if relevant_moves:
                        moves_per_stone = " | ".join(relevant_moves)
                        encoding.append(f"(({same_pos}) -> ({moves_per_stone}))")

    return ' & \n'.join(encoding)


def encode_not_moving_stones(initial_state, goal_state, size=9):
    encoding = []
    # encode where stones are not
    for idx, stone in enumerate(range(1, size)):
        encoding.append(f"\n")
        if initial_state[idx] == goal_state[idx]:
            pos = POSITIONS[idx]
            # add mv action for same pos - don't add those to all_moves since no need to waste time on already correct
            encoding.append(f"stone_{stone}_{pos}_{N} & ")
            for p in POSITIONS:
                if p != pos:
                    encoding.append(
                        f"!stone_{stone}_{p}_{N} &")  # only add stone add correct pos since no move

    return ' '.join(encoding)


# ToDo: Change to any possible initial state and input steps taken
initial_state = [1, 2, 3, 8, 7, 4, 6, 5, 0]  # 12 steps
# initial_state =  [1, 2, 3, 4, 5, 6, 0, 7, 8]  # 2 steps
# initial_state = [1, 2, 3, 0, 5, 6, 4, 7, 8] # 3 steps

f.write('\n %% init state\n')
# stone_1_A_0 & stone_2_B_0 & stone_3_C_0 & stone_8_D_0 & ...
# & !stone_1_B_0 & !stone_1_C_0 & ... define where stone can NOT be
encoded_initial_state = encode_state(initial_state, '0') # starting at t=0
f.write(encoded_initial_state)

goal_state = [1, 2, 3, 4, 5, 6, 7, 8, 0]

f.write('\n %% goal state\n')
# stone_1_A_n & stone_2_B_n & stone_3_C_n & stone_4_D_n & ...
# & !stone_2_A_n & !stone_2_C_n & !stone_2_D_n & ...
# define where stone can NOT be - XOR not necessary since only 1 Goal state
encoded_goal_state = encode_state(goal_state, str(N))
f.write(encoded_goal_state)


# if stone is already in correct position - Not necessarily needed ??
#encoded_not_moving = encode_not_moving_stones(initial_state, goal_state)
#f.write('\n % stones with correct position in the beginning\n')
#f.write(encoded_not_moving)

# execute actions
f.write('%% actions\n')
# mv_5_HI_0 -> ((stone_5_H_0 & !stone_5_I_0 ..?) & (!stone_5_H_1 & stone_5_I_1)) #rest pos NOT?
# do for every time step
encoded_moves = encode_moves()
f.write(encoded_moves)

# exactly 1 action
f.write('%% exactly 1 action\n')
# (mv_5_HI_0 | mv_6_GH_0 | ...) & (!mv_5_HI_0 | !mv_6_GH_0 | !...)
encoded_one_move = encode_exact_one_move()
f.write(encoded_one_move)  # 9.6MB???

# frame axioms
f.write('\n %% frame axioms\n')
f.write('& \n')
# ((stone_5_H_0 & !stone_5_H_1) -> mv_5_HI_0) &...
# stone moved to another position and not there anymore - action must have been executed
encoded_frame_axioms = encode_frame_axioms()
f.write(encoded_frame_axioms)

f.write('\n %% frame axioms 2\n')
f.write('& \n')
# if stone now at position where it wasn't before
encoded_frame_axioms2 = encode_frame_axioms2()
f.write(encoded_frame_axioms2)

# Limboole http://fmv.jku.at/limboole
