from enum import Enum
from collections import deque
import copy
from flask import Flask, render_template, jsonify,json,request
# from flask_sqlalchemy import SQLAlchemy
import json

app = Flask(__name__)

global_time = 10

class CommitmentStatus(Enum):
    ACT = 1
    BAS = 2
    SAT = 3
    EXP = 4
    VIO = 5


# 博弈树节点信息：承诺：commitment，孩子节点列表：children，父节点：parent
class TreeNode:
    _id_counter = 0  # Class-level variable to keep track of IDs
    def __init__(self, commitments, parent=None):
        self.ID = TreeNode._id_counter  # Assign a unique ID to each node
        TreeNode._id_counter += 1  # Increment the ID counter
        self.commitments = commitments
        self.children = []
        self.parent = parent
        self.player = "root"
        self.payoff = None

    def add_child(self, child):
        self.children.append(child)
    
    def reset_id_counter():
        TreeNode._id_counter = 0
    
    # 初始化一个全是ACT状态的根节点
    # 根节点的孩子节点是无条件承诺的n个节点，n=玩家个数
    def init(self,parent = None):
        players = set()
        for commitment in self.commitments:
            if commitment.initiators[0] not in players:
                players.add(commitment.initiators[0])
            if commitment.receivers[0] not in players:
                players.add(commitment.receivers[0])
                
                
        for i in range(len(self.commitments)):
            self.commitments[i].status = CommitmentStatus.ACT
            self.commitments[i].p = False
            self.commitments[i].r = False
            self.commitments[i].tc = False


        commitments_cp = copy.deepcopy(self.commitments)
        for i in range(len(commitments_cp)):
            if commitments_cp[i].Prerequisites == None:
                commitments_cp[i].status = CommitmentStatus.BAS
                
                
        for player in players:
            for i in range(len(self.commitments)):
                if commitments[i].initiators[0] == player:
                    flag = True
                    if commitments[i].Prerequisites == None:
                        child_node = TreeNode(commitments=commitments_cp,parent=self)
                        child_node.player = player
                        self.children.append(child_node)
                        break
                    for key,value in commitments[i].Prerequisites.items():
                        dependent_state = None
                        if value == 'sat':
                            dependent_state = CommitmentStatus.SAT
                        elif value == 'exp':
                            dependent_state = CommitmentStatus.EXP
                        elif value == 'vio':
                            dependent_state = CommitmentStatus.VIO
                        key = int(key) - 1
                        flag = flag and commitments[key].status == dependent_state
                    if flag:                               
                        child_node = TreeNode(commitments=commitments_cp,parent=self)
                        child_node.player = player
                        self.children.append(child_node)
                        break
                    

    # 打印树的结构
    def __str__(self, level=0):
        status = list()
        for term in self.commitments:
            status.append(term.status)
        ret = "\t" * level + f"{[e for e in status]}" + "\n"+"\n"
        for child in self.children:
            ret += child.__str__(level + 1)
        return ret
    
    def __hash__(self):
        # Using the hash of commitment tuples and other attributes
        commitments_hash = hash(tuple(
            frozenset((
                commitment.commitment_id,
                commitment.status,
                tuple(commitment.initiators[0]),
                tuple(commitment.receivers[0]),
                tuple(sorted(commitment.Prerequisites.items() if commitment.Prerequisites else [])),
                commitment.time,
                tuple(commitment.Allpayoff) if commitment.Allpayoff else None
            ))
            for commitment in self.commitments
        ))

        return hash((commitments_hash, self.parent, self.player))
    
    
# 求树的高度、叶子节点数量、节点总数量
def tree_properties(root):
    if not root:
        return 0, 0, 0  # 如果树为空，高度、叶子节点数和总节点数均为0

    height = 0
    leaf_count = 0
    total_nodes = 0

    queue = deque([(root, 1)])  # 使用元组表示节点和其深度

    while queue:
        current_node, depth = queue.popleft()
        height = max(height, depth)
        total_nodes += 1

        if not current_node.children:
            leaf_count += 1
        else:
            for child in current_node.children:
                queue.append((child, depth + 1))

    return height, leaf_count, total_nodes
    
    
def parse_commitment_file(file_path):
    commitments = []
    with open(file_path, 'r', encoding='utf-8') as file:
        for line in file:
            values = line.strip().split(';')
            print("values = ",values)
            commitment_id = str(len(commitments) + 1)
            initiators = values[0].split(',')
            receivers = values[1].split(',')
            p = values[2].split(',')
            r = values[3].split(' ')
            # 时间有两个（act_time_out,bas_time_out）
            time = values[4].split(' ')
            payoff = values[5].split(' ')
            commitments.append((commitment_id, initiators, receivers, p, r, time,payoff))
    return commitments


# 承诺类，仅用于初始化，后续的状态转移用因果图实现
class Commitment:
    global global_time
    def __init__(self, commitment_id, initiators, receivers, Prerequisites, result, time,payoff = None):
        # 承诺id
        self.commitment_id = commitment_id
        # 动作发出者（可能是多个）
        self.initiators = initiators
        # 动作接受者（可能是多个）
        self.receivers = receivers
        # 三个布尔变量 p r tc 用于确定当前承诺的状态
        # 前提条件 [依赖承诺id：依赖承诺状态]
        
        # 结果
        self.r = False
        self.result = result
        result_dependent = list()
        if len(result) != 1:
            for i in range(1,len(result),1):
                result_dependent.append(result[i])
        result = result[0]
        
        if result_dependent == '':
            self.result_Prerequisites = None
        else:
            self.result_Prerequisites = {int(pair.split(':')[0]): pair.split(':')[1] for pair in result_dependent}
        
        # 时间
        self.time = int(time[0])
        self.time_vio = int(time[1])
        # payoff [SAT_PAYOFF,EXP_PAYOFF,VIO_PAYOFF]
        self.Allpayoff = payoff
        # 当前承诺最终状态的收益
        self.finalpayoff = None
        if self.time < global_time:
            self.tc = True
        else:
            self.tc = False
        if Prerequisites[0] == '':
            self.status = CommitmentStatus.BAS
            self.p = True
        else:
            self.status = CommitmentStatus.ACT
            self.p = False
        # 用字典存合约之间的依赖关系
        if Prerequisites[0] == '':
            self.Prerequisites = None
        else:
            self.Prerequisites = {int(pair.split(':')[0]): pair.split(':')[1] for pair in Prerequisites}
        # 承诺状态的最终收益
        if self.status == CommitmentStatus.SAT:
            self.finalpayoff = self.Allpayoff[0]
        elif self.status == CommitmentStatus.EXP:
            self.finalpayoff = self.Allpayoff[1]
        elif self.status == CommitmentStatus.VIO:
            self.finalpayoff = self.Allpayoff[2]
            
    def __eq__(self, other):
        if isinstance(other, Commitment):
            return (
                self.commitment_id == other.commitment_id and
                self.initiators == other.initiators and
                self.receivers == other.receivers and
                self.Prerequisites == other.Prerequisites and
                self.result == other.result and
                self.time == other.time and
                self.Allpayoff == other.Allpayoff
            )
        return False

    def __hash__(self):
        # 使用属性值的哈希值来生成类的哈希值
        return hash((
            self.commitment_id,
            tuple(self.initiators),
            tuple(self.receivers),
            tuple(sorted(self.Prerequisites.items() if self.Prerequisites else [])),
            self.result,
            self.time,
            tuple(self.Allpayoff) if self.Allpayoff else None
        ))

# 判断是否有相同的类实例
# def has_duplicate_objects(commitment_list,treeNode):
#     seen = set()
#     for obj in commitment_list:
#         if obj in seen:
#             return True
#         seen.add(obj)
#     return False

def has_duplicate_nodes(node_list):
    seen_nodes = set()
    for node in node_list:
        status_list = [e.status.value for e in node.commitments]
        if str(status_list) in seen_nodes:
            return True
        else:
            seen_nodes.add(str(status_list))
    return False


def get_commitments(commitments_data):
    commitments_init = []
    for commitment_data in commitments_data:
        commitments_init.append(Commitment(*commitment_data))
    return commitments_init


# 生成依赖图
def get_dependent_graph(commitments):
    dependent_graph = {}
    for commitment in commitments:
        dependent_graph[int(commitment.commitment_id)] = []
        print("commitment.commitment_id = ",commitment.commitment_id)
        print("commitment.Prerequisites = ",commitment.Prerequisites)
        print("commitment.result_Prerequisites = ",commitment.result_Prerequisites)
    for commitment in commitments:
        if commitment.Prerequisites is None:
            continue
        for key, value in commitment.Prerequisites.items():
            dependent_graph[key].append(("p",int(commitment.commitment_id)))
    for commitment in commitments:
        for key,value in commitment.result_Prerequisites.items():
            dependent_graph[key].append(("r",int(commitment.commitment_id)))
    return dependent_graph


# 拓扑排序，检查是否有环、时间冲突
def topological_sort(dependent_graph,commitments): 
    in_degree = {node: 0 for node in dependent_graph}
    print("____topological_sort_____")
    print("in_degree = ",in_degree)
    print("dependent_graph.values() = ",dependent_graph.values())
    for dependencies in dependent_graph.values():
        for dependency in dependencies:
            in_degree[dependency] += 1

    queue = deque([node for node in in_degree if in_degree[node] == 0])
    result = []

    while queue:
        current_node = queue.popleft()
        result.append(current_node)

        for neighbor in dependent_graph.get(current_node, []):
            in_degree[neighbor] -= 1
            if in_degree[neighbor] == 0:
                queue.append(neighbor)

    if len(result) == len(dependent_graph):
        return result
    else:
        # 存在环，图中有向图不是DAG
        raise ValueError("Graph contains a cycle")


# 根据依赖的状态改变当前节点的状态至可能的最终状态
# EXP要放在ACT->BAS之后，因为ACT->BAS是瞬间动作
def change_state(commitments):
    convert_to_bas = False
    act_index = list()
    dependent_index = -1
    for i in range(len(commitments)):
        if commitments[i].status in (CommitmentStatus.SAT,CommitmentStatus.EXP,CommitmentStatus.VIO):
            if commitments[i].status == CommitmentStatus.SAT:
                commitments[i].r = True
            else:
                commitments[i].r = False
                commitments[i].tc = False
            continue
        # 用dependent_graph确定孩子节点的状态
        flag = True
        if commitments[i].Prerequisites == None:
            continue
        for key,value in commitments[i].Prerequisites.items():
            dependent_state = None
            if value == 'sat':
                dependent_state = CommitmentStatus.SAT
            elif value == 'exp':
                dependent_state = CommitmentStatus.EXP
            elif value == 'vio':
                dependent_state = CommitmentStatus.VIO
            key = int(key) - 1
            flag = flag and commitments[key].status == dependent_state
            
        if flag:
            commitments[i].p = True
            commitments[i].status = CommitmentStatus.BAS
            convert_to_bas = True
            dependent_index = i
            # 返回就绪态的节点，需要生成分支
        elif not flag and commitments[i].status == CommitmentStatus.BAS:
            commitments[i].status = CommitmentStatus.VIO
            commitments[i].r = False
            commitments[i].tc = False
        elif not flag and commitments[i].status == CommitmentStatus.ACT:
            act_index.append(i)
            
    # 如果依赖的条款状态不是最终态，ACT不能转换为EXP，如果依赖的条款是最终态，但是不能让ACT转变为BAS，这时ACT->EXP 
    changed_to_EXP_index_set = set()
    for index in act_index:
        act_to_exp = True
        dependent_keys_set = set(commitments[index].Prerequisites.keys())
        # 当前承诺不依赖于上一个状态变迁的承诺，可以直接变到最终态
        if dependent_index + 1 not in dependent_keys_set:
            print("dependent_index = ",dependent_index,"dependent_keys_set = ",dependent_keys_set)
            for require_index,pre_requisite in commitments[index].Prerequisites.items():
                require_index = require_index - 1
                act_to_exp = act_to_exp and commitments[require_index].status in (CommitmentStatus.SAT,CommitmentStatus.EXP,CommitmentStatus.VIO)
                print("index = ",index,"require_index = ",require_index,"commitments[require_index].status = ",commitments[require_index].status)
            if act_to_exp:
                commitments[index].status = CommitmentStatus.EXP
                # 记录本轮状态变迁的承诺id
                changed_to_EXP_index_set.add(index+1)
            else:
                continue
    if convert_to_bas:
        for index in act_index:
            for require_index,pre_requisite in commitments[index].Prerequisites.items():
                if require_index in changed_to_EXP_index_set:
                    commitments[index].status = CommitmentStatus.ACT
    # 返回最终态的节点，不需要生成分支（需要给出收益）
    # print(f"change state commitments = ",commitments)
    return commitments


# 返回当前节点的孩子节点，分成player_1 ～ player_n
# 当前节点只能有一个玩家做动作
def get_child(node):
    player_child_node_list = list()
    player_commitments_index = list()
    commitments = node.commitments
    player = node.player
    # 找出发出者是玩家1和玩家2的承诺索引和状态（index，status）
    # 通过承诺的timeout时间对状态排序，如果当前顺序中存在状态为BAS的承诺，则会分裂出多个节点
    # 根据BAS->SAT的可能时间生成树中某一层的节点
    for i in range(len(commitments)):
        if commitments[i].status in (CommitmentStatus.SAT,CommitmentStatus.EXP,CommitmentStatus.VIO):
            continue
        # 分别获取player1和player2的未到最终态的承诺索引
        if commitments[i].initiators[0] == player:
            player_commitments_index.append(i)      
    # player1_action_index_status_time = sorted(player1_action_index_status_time,key = lambda x:x[2])
    # player2_action_index_status_time = sorted(player2_action_index_status_time,key = lambda x:x[2])
    player_child_node_list = get_player_child_list(node = copy.deepcopy(node),player_commitments_index = player_commitments_index)
    # player2_child_node_list = get_player_child_list(commitments = copy.deepcopy(commitments),player_commitments_index = player2_commitments_index)
    # for i in range(len(commitments)):
    #     # 当前承诺的状态是最终态，直接跳过
    #     if commitments[i].status in (CommitmentStatus.EXP,CommitmentStatus.VIO,CommitmentStatus.SAT):
    #         continue
    #     # 承诺状态是激活态，依赖的承诺状态符合前提条件，直接转变为就绪态
    #     # 就绪态会产生两个分支：sat和vio，传入change_satate确定孩子节点的最终状态
    #     elif commitments[i].status == CommitmentStatus.BAS:
    #         commitments[i].status = CommitmentStatus.SAT
    #         sat_commitments = commitments
    #         child_node_list.append(change_state(copy.deepcopy(sat_commitments)))
    #         commitments[i].status = CommitmentStatus.VIO
    #         vio_commitments = commitments
    #         child_node_list.append(change_state(copy.deepcopy(vio_commitments)))
    return player_child_node_list


# 一个承诺的所有依赖都没有到达最终态时，它的状态保持原样
# 一个承诺的依赖中有一个到达最终态，但不是依赖的状态，这个承诺的状态直接变成4
# 用因果图来确定承诺的最终状态
def inspect_final_state(commitments):
    global dependent_graph
    print("dependent_graph = ",dependent_graph)
    print("----- inspect_final_state 传入 commitments status = -----",[e.status.value for e in commitments])
    final_status_index = set()
    act_index_time_index = list()
    for i in range(len(commitments)):
        if commitments[i].status in (CommitmentStatus.SAT,CommitmentStatus.EXP,CommitmentStatus.VIO):
            final_status_index.add(i+1)
        elif commitments[i].status == CommitmentStatus.ACT:
            act_index_time_index.append((i,commitments[i].time))
    sorted(act_index_time_index,key = lambda x:x[1])
    for index,time in act_index_time_index:
        all_dependent_satisfied = True
        has_final_dependent = True
        one_dependent_not_sat = False
        for key,value in commitments[index].Prerequisites.items():
            dependent_state = None
            if value == 'sat':
                dependent_state = CommitmentStatus.SAT
            elif value == 'exp':
                dependent_state = CommitmentStatus.EXP
            elif value == 'vio':
                dependent_state = CommitmentStatus.VIO
            key = int(key) - 1
            has_final_dependent = has_final_dependent and (key+1) in final_status_index
            if key+1 in final_status_index:
                all_dependent_satisfied = all_dependent_satisfied and commitments[key].status == dependent_state
                if commitments[key].status != dependent_state:
                    one_dependent_not_sat = True
                
        if has_final_dependent:
            if all_dependent_satisfied:
                print("all_dependent_satisfied,commitments status before bas = ",[e.status.value for e in commitments])
                commitments[index].status = CommitmentStatus.BAS
                print("all_dependent_satisfied,commitments status after bas = ",[e.status.value for e in commitments])
            else:
                commitments[index].status = CommitmentStatus.EXP
                final_status_index.add(index+1)
        else:
            if one_dependent_not_sat:
                if commitments[index].status == CommitmentStatus.ACT:
                    commitments[index].status = CommitmentStatus.EXP

            
    print("----- inspect_final_state 传出 commitments status = -----",[e.status.value for e in commitments])
    return commitments
    

# 第二版状态函数
# 传入一个承诺合集，根据依赖关系确定当前的可能状态，固定某个player
# 如果某个承诺的前提条件都不可能被满足：依赖承诺的状态是最终态，但和前提中的状态不一致，则直接变成最终态
# 如果某个承诺的前提条件有可能被满足：依赖承诺的状态是ACT或者BAS
def get_final_state(node,cur_time):
    global dependent_graph
    print()
    commitments = node.commitments
    print("__get_final_state__start__",f"commitments_status = {[e.status.value for e in commitments]}")
    player = node.player
    player_index_status_time = list()
    index_status_time = list()
    # 重建player的承诺信息
    for i in range(len(commitments)):
        if commitments[i].initiators[0] == player:
            player_index_status_time.append((i,commitments[i].status,commitments[i].time))
    player_index_status_time = sorted(player_index_status_time,key = lambda x:x[2])
    
    for i in range(len(commitments)):
        if commitments[i].status == CommitmentStatus.ACT or commitments[i].status == CommitmentStatus.EXP:
            index_status_time.append((i,commitments[i].status,commitments[i].time))
        else:
            index_status_time.append((i,commitments[i].status,commitments[i].time_vio))
    index_status_time = sorted(index_status_time,key = lambda x:x[2])
    print(f"___before_time_out_____cur_time = {cur_time},commitments_status = {[e.status.value for e in commitments]}")
    
    for i in range(len(commitments)):
        if commitments[i].status == CommitmentStatus.ACT and commitments[i].time <= cur_time:
            flag = True
            for key,value in commitments[i].Prerequisites.items():
                dependent_state = None
                if value == 'sat':
                    dependent_state = CommitmentStatus.SAT
                elif value == 'exp':
                    dependent_state = CommitmentStatus.EXP
                elif value == 'vio':
                    dependent_state = CommitmentStatus.VIO
                key = int(key) - 1
                flag = flag and commitments[key].status == dependent_state
            if flag:
                commitments[i].status = CommitmentStatus.BAS
            else:
                commitments[i].status = CommitmentStatus.EXP
        elif commitments[i].status == CommitmentStatus.BAS and commitments[i].time_vio < cur_time:
            print(f"___commitments[i]_is_bas_____cur_time = {cur_time},commitments_status = {[e.status.value for e in commitments]}")
            commitments[i].status = CommitmentStatus.VIO
    print(f"___after_time_out_____cur_time = {cur_time},commitments_status = {[e.status.value for e in commitments]}")
                    
    # 存当前玩家到达最终态的承诺id和承诺状态
    final_status_id_set = set()
    for index,status,time in index_status_time:
        if commitments[index].status in (CommitmentStatus.SAT,CommitmentStatus.EXP,CommitmentStatus.VIO):
            final_status_id_set.add(index+1)
            
    for i in range(len(commitments)):
        flag = True
        can_be_infected = True
        if commitments[i].status in (CommitmentStatus.SAT,CommitmentStatus.EXP,CommitmentStatus.VIO):
            continue
        
        if commitments[i].Prerequisites == None:
            commitments[i].status = CommitmentStatus.BAS
            continue
        
        for key,value in commitments[i].Prerequisites.items():
            dependent_state = None
            if value == 'sat':
                dependent_state = CommitmentStatus.SAT
            elif value == 'exp':
                dependent_state = CommitmentStatus.EXP
            elif value == 'vio':
                dependent_state = CommitmentStatus.VIO
            key = int(key) - 1
            if key+1 in final_status_id_set:
                flag = flag and commitments[key].status == dependent_state
            else:
                can_be_infected = False
                break
            # if commitments[key].status in (CommitmentStatus.SAT,CommitmentStatus.EXP,CommitmentStatus.VIO):
            #     flag = flag and commitments[key].status == dependent_state
        if can_be_infected:
            final_status_id_set.add(i+1)
            if not flag:
                if commitments[i].status == CommitmentStatus.ACT:
                    commitments[i].status = CommitmentStatus.EXP
                elif commitments[i].status == CommitmentStatus.BAS:
                    commitments[i].status = CommitmentStatus.VIO
            else:
                if commitments[i].status == CommitmentStatus.ACT:
                    commitments[i].status = CommitmentStatus.BAS
                    final_status_id_set.remove(i+1)
    print("__get_final_state__end__",f"commitments_status = {[e.status.value for e in commitments]}")
    return inspect_final_state(commitments)



# 传入某个player的commitments_index，返回这个player的所有孩子节点
# 现在返回的孩子节点中不是只有一个玩家可以做动作，需要用player标识当前传入的节点
# 判断输入节点能不能继续做动作，如果不能就删除这个节点，
def get_player_child_list(node,player_commitments_index):
    print()
    print("-----get_player_child_list-----start-----")
    print("----- 传入 commitments status = -----",[e.status.value for e in node.commitments],"player = ",node.player)
    child_node_list = list()
    BAS_position = 0
    index_status_time = list()
    player_status = set()
    commitments = node.commitments
    all_index_status_time = list()
    for index in player_commitments_index:
        if commitments[index].status == CommitmentStatus.ACT:
            index_status_time.append((index,commitments[index].status,commitments[index].time))
        elif commitments[index].status == CommitmentStatus.BAS:
            index_status_time.append((index,commitments[index].status,commitments[index].time_vio))
        player_status.add(commitments[index].status)
    for i in range(len(commitments)):
        if commitments[i].status == CommitmentStatus.ACT or commitments[i].status == CommitmentStatus.EXP:
            all_index_status_time.append((i,commitments[i].status,commitments[i].time))
        else:
            all_index_status_time.append((i,commitments[i].status,commitments[i].time_vio))
    index_status_time = sorted(index_status_time,key = lambda x:x[2])
    all_index_status_time = sorted(all_index_status_time,key = lambda x:x[2])
    # 判断当前玩家有没有可以做动作的bas承诺
    # 找到BAS的位置，BAS_position用来记录BAS完成之前有几个承诺可能超时
    bas_effect = False
    for index,status,time in index_status_time:
        if commitments[index].status == CommitmentStatus.BAS and not commitments[index].result_Prerequisites:
            bas_effect = True
            break
        BAS_position += 1
        
    # 找到BAS在index_status_time中的位置，模拟在不同时间点转换为SAT
    # 如果某一个player的承诺没有BAS状态，直接用EXP的时间和承诺依赖关系判断
    if bas_effect:
        print("-----BAS_IN_PLAYER_STATUS-----")
        # 记录含有BAS承诺集合的初始状态，BAS->VIO时用
        init_BAS_commitments = commitments
        print("所有承诺的状态按照时间排序 all_index_status_time = ",[(e,f.value,g) for e,f,g in all_index_status_time])
        print(f"当前玩家 player = {node.player} player status index =",[(e[0],e[1].value,e[2]) for e in index_status_time],"-----bas position---- = ",BAS_position)
        # BAS在第一个位置，没有承诺会因为BAS的时间超时，BAS->SAT
        if BAS_position == 0:
            cur_time = commitments[index_status_time[BAS_position][0]].time_vio
            commitments[index_status_time[BAS_position][0]].status = CommitmentStatus.SAT
            for i in range(len(commitments)):
                if commitments[i].status == CommitmentStatus.ACT and commitments[i].time <= cur_time:
                    commitments[i].status = CommitmentStatus.EXP
                elif commitments[i].status == CommitmentStatus.BAS and commitments[i].time_vio < cur_time:
                    commitments[i].status = CommitmentStatus.VIO
            print(f"BAS_POSITION = 0 cur_time = {cur_time} time out iter after status =",[e.status.value for e in commitments])
            node.commitments = commitments
            bas_0_commitments_final_state = get_final_state(node=copy.deepcopy(node),cur_time=cur_time)
            child_node_list.append(TreeNode(commitments=get_final_state(copy.deepcopy(node),cur_time=cur_time)))
            print("BAS_POSITION = 0 final state = ",[e.status.value for e in bas_0_commitments_final_state])
        else:
            # 先假设只有一个BAS状态，获取BAS的位置，模拟在不同时间变成SAT
            # 由于BAS一定会转变为SAT，先把最早变成SAT的节点直接加入到child_node_list中
            node.commitments[index_status_time[BAS_position][0]].status = CommitmentStatus.SAT
            # child_node_list.append(TreeNode(commitments=get_final_state(copy.deepcopy(commitments),index_status_time=index_status_time)))
            # BAS_index = index_status_time[BAS_position][0]
            # for i in range(BAS_position):
            #     if commitments[i].status == CommitmentStatus.ACT:
            #         commitments[i].status = CommitmentStatus.EXP
            cur_time = commitments[BAS_position].time_vio
            for i in range(len(commitments)):
                if commitments[i].status == CommitmentStatus.ACT and commitments[i].time <= cur_time:
                    commitments[i].status = CommitmentStatus.EXP
                elif commitments[i].status == CommitmentStatus.BAS and commitments[i].time_vio < cur_time:
                    commitments[i].status = CommitmentStatus.VIO
            node.commitments = commitments
            commitments_cp = get_final_state(copy.deepcopy(node),cur_time=cur_time)
            print("BAS != 0, get final state commitments_cp.status = ",[e.status.value for e in commitments_cp])
            # player还没有确定，暂定是父节点的player，build_tree时看一下有哪个玩家的承诺还没有到达最终态，分裂成若干节点
            newNode = TreeNode(commitments=commitments_cp)
            newNode.player = node.player
            child_node_list.append(newNode)
            if has_duplicate_nodes(child_node_list):
                child_node_list.pop()
            # for i in range(BAS_position):
            #     if index_status_time[i][1] == CommitmentStatus.ACT:
            #         commitments[index_status_time[i][0]].status = CommitmentStatus.EXP
            #         commitments_cp = get_final_state(copy.deepcopy(commitments),index_status_time=index_status_time)
            #         child_node_list.append(TreeNode(commitments=commitments_cp))
            #         flag = has_duplicate_objects(child_node_list)
            #         if flag:
            #             child_node_list.pop()
            #             continue
            # print("BAS_position = ",BAS_position,"index_status_time = ",index_status_time)
        # 有BAS就会有VIO，最后加上这个状态
        init_BAS_commitments[index_status_time[BAS_position][0]].status = CommitmentStatus.VIO
        cur_time = init_BAS_commitments[index_status_time[BAS_position][0]].time_vio
        for i in range(len(init_BAS_commitments)):
            if init_BAS_commitments[i].status == CommitmentStatus.ACT and init_BAS_commitments[i].time <= cur_time:
                init_BAS_commitments[i].status = CommitmentStatus.EXP
            elif init_BAS_commitments[i].status == CommitmentStatus.BAS and init_BAS_commitments[i].time_vio < cur_time:
                init_BAS_commitments[i].status = CommitmentStatus.VIO
        node.commitments = init_BAS_commitments
        init_BAS_commitments_final_state = get_final_state(node=copy.deepcopy(node),cur_time=cur_time)
        print("init_BAS_commitments_final_state = ",[e.status.value for e in init_BAS_commitments_final_state])
        # get_final_state只能由当前玩家的状态改变，影响到其他玩家的状态，不能把整个节点的状态全都扫一遍，需要修改
        child_node_list.append(TreeNode(commitments=get_final_state(copy.deepcopy(TreeNode(commitments=init_BAS_commitments)),cur_time=cur_time)))
        if has_duplicate_nodes(child_node_list):
            child_node_list.pop()
    else:
        for index,status,time in index_status_time:
            print("__BAS_NOT_IN_PLAYER_STATUS__","commitments_status = ",[e.status.value for e in commitments],"index_status_time = ",[(e,f.value,g) for e,f,g in index_status_time])
            cur_time = commitments[index].time
            for i in range(len(commitments)):
                if commitments[i].status == CommitmentStatus.ACT and commitments[i].time <= cur_time:
                    commitments[i].status = CommitmentStatus.EXP
                elif commitments[i].status == CommitmentStatus.BAS and commitments[i].time_vio < cur_time:
                    commitments[i].status = CommitmentStatus.VIO
            commitments_cp = get_final_state(copy.deepcopy(TreeNode(commitments=commitments)),cur_time=cur_time)
            print("BAS NOT IN PLAYER STATUS, get final state commitments_cp.status = ",[e.status.value for e in commitments_cp])
            child_node_list.append(TreeNode(commitments = commitments_cp))
            if has_duplicate_nodes(child_node_list):
                print("pop has duplicated object")
                child_node_list.pop()
    print("-----get_player_child_list-----end-----")
    return child_node_list


# 判断是否为最终状态，如果是则返回收益payoff
def is_final(commitments):
    flag = True
    position = -1
    for i in range(len(commitments)):
        flag = flag and commitments[i].status in (CommitmentStatus.EXP,CommitmentStatus.VIO,CommitmentStatus.SAT)
        if commitments[i].status == CommitmentStatus.SAT:
            commitments[i].finalpayoff = commitments[i].Allpayoff[0]
        elif commitments[i].status == CommitmentStatus.EXP:
            commitments[i].finalpayoff = commitments[i].Allpayoff[1]
        elif commitments[i].status == CommitmentStatus.VIO:
            commitments[i].finalpayoff = commitments[i].Allpayoff[2]
    for i in range(len(commitments)):
        if commitments[i].status not in (CommitmentStatus.EXP,CommitmentStatus.VIO,CommitmentStatus.SAT):
            position = i -1
            break
    if flag:
        return True,commitments,position
    else:
        return False,commitments,position


def player_has_actions(commitments,player):
    print("____player_has_actions____START")
    print("player_has_actions commitments[i].status = ",[e.status.value for e in commitments],"player = ",player)
    for i in range(len(commitments)):
        if commitments[i].status in (CommitmentStatus.EXP,CommitmentStatus.VIO,CommitmentStatus.SAT):
            print("Continue: commitment_id = ",i+1,"commitments[i].status = ",commitments[i].status.value)
            continue
        if commitments[i].initiators[0] == player and commitments[i].status == CommitmentStatus.BAS:
            print("player has bas status commitments[i].status = ",[e.status.value for e in commitments],"player = ",player)
            return True
    print("player doesn't has bas status commitments[i].status = ",[e.status.value for e in commitments],"player = ",player)
    print("____player_has_actions____END")
    return False
    

# 构建博弈树
# 初始化一个全是ACT状态的根节点，然后分裂成各玩家的状态节点
# 如果有一个节点存在k个玩家的动作，这个节点复制k份，全都作为父节点的孩子
def build_tree(commitments):
    root = TreeNode(commitments=commitments,parent=None)
    root.init()
    queue = deque()
    # 如果root的孩子节点中只有一个玩家可以做动作，则直接把这个孩子作为root入队
    # 否则保留root，把root的孩子节点入队
    if len(root.children) == 1:
        root = root.children[0]
        queue.append(root)
    else:
        for child in root.children:
            queue.append(child)
    while queue:
        other_players = set()
        left_players = set()
        cur_node = queue.popleft()
        # 遍历未到达最终态的承诺的玩家
        for commitment in cur_node.commitments:
            if commitment.status in (CommitmentStatus.EXP,CommitmentStatus.VIO,CommitmentStatus.SAT):
                continue
            if commitment.initiators[0] not in left_players:
                left_players.add(commitment.initiators[0])
        # 输入当前节点，返回它的所有孩子节点
        cur_node_children = get_child(copy.deepcopy(cur_node))
        for cur_node_child in cur_node_children:
            cur_node_child.player = cur_node.player
            isfinal,payoff_commitments,position = is_final(copy.deepcopy(cur_node_child.commitments))
            if isfinal:
                player1_payoff = 0
                player2_payoff = 0
                for commitment in payoff_commitments:
                    print("final payoff = ",commitment.finalpayoff)
                    player1_payoff += eval(commitment.finalpayoff)[0]
                    player2_payoff += eval(commitment.finalpayoff)[1]
                cur_node_child.commitments = payoff_commitments
                cur_node_child.payoff = (player1_payoff,player2_payoff)
                cur_node.add_child(cur_node_child)
            else:
                only_one_player = True
                has_cur_node_player = False
                for commitment in cur_node_child.commitments:
                    if commitment.status in (CommitmentStatus.EXP,CommitmentStatus.VIO,CommitmentStatus.SAT):
                        continue
                    only_one_player = only_one_player and commitment.initiators[0] == cur_node_child.player
                    if commitment.initiators[0] != cur_node_child.player:
                        other_players.add(commitment.initiators[0])
                    else:
                        has_cur_node_player = True
                if has_cur_node_player and player_has_actions(cur_node_child.commitments,cur_node_child.player):
                    cur_node_child_cp = copy.deepcopy(cur_node_child)
                    cur_node.add_child(cur_node_child_cp)
                    queue.append(cur_node_child_cp)
                if not only_one_player:
                    for other_player in other_players:
                        if player_has_actions(cur_node_child.commitments,other_player):
                            cur_node_child.player = other_player
                            other_player_child = copy.deepcopy(cur_node_child)                            
                            cur_node.add_child(other_player_child)       
                            queue.append(other_player_child)             
        # for result_commitments in result_commitments_list:
        #     # 如果是最终态，不需要生成新的分支，不入队,直接给出收益
        #     isfinal,payoff_commitments,position = is_final(copy.deepcopy(result_commitments))
        #     if isfinal:
        #         cur_node.add_child(TreeNode(commitments=payoff_commitments,parent=cur_node))
        #     # 如果不是最终态，入队
        #     else:
        #         child = TreeNode(commitments=payoff_commitments,parent=cur_node)
        #         cur_node.add_child(child)
        #         queue.append(child) 
    return root


def level_order_traversal(root):
    if not root:
        return

    result = []
    queue = deque([root])

    while queue:
        current_node = queue.popleft()
        result.append(current_node.commitments)

        for child in current_node.children:
            queue.append(child)

    return result  
  
def compute_equilibrium(root):
    if not root:
        return []

    result = []
    stack = []
    current = root
    last_visited = None

    while stack or current:
        if current:
            stack.append(current)
            current = current.children[0]
        else:
            peek_node = stack[-1]
            if peek_node.children and peek_node.children[0] != last_visited and peek_node.children[1] != last_visited:
                current = peek_node.children[1]
            else:
                result.append(peek_node)
                last_visited = stack.pop()

    return result

file_path = "./13-commitments.txt"
commitments_data = parse_commitment_file(file_path)
commitments = get_commitments(commitments_data)

# for commimet in commitments:
#     print(commimet.__dict__)
    
dependent_graph = get_dependent_graph(commitments)
print(dependent_graph)
# try:
#     sorted_result = topological_sort(dependent_graph,commitments)
#     print("Topological Sort Result:", sorted_result)
# except ValueError as e:
#     print(f"Error: {e}")
# print("dependent graph = ",dependent_graph)
tree_root = build_tree(commitments=commitments)
depth,width,total_node_num = tree_properties(tree_root)



def serialize_enum(obj):
    if isinstance(obj, Enum):
        return obj.value
    raise TypeError(f"Object of type {type(obj)} is not JSON serializable")

@app.route('/')
def render_tree_page():
    return render_template('index.html')

@app.route('/get_tree_data', methods=['GET'])
def get_tree_data():
    tree_root = build_tree(commitments=commitments)
    tree_data = json.dumps({'tree_data': convert_tree_to_dict(tree_root)}, default=serialize_enum)
    print("tree_data = ",tree_data)    
    return tree_data

def convert_tree_to_dict(node):
    node_data = {
        'name': f"{[e.status.value for e in node.commitments]}",  # Use a relevant attribute as the name
        'data': [vars(commitment) for commitment in node.commitments],
        'children': [convert_tree_to_dict(child) for child in node.children],
        'player' : f"{node.player}",
        'depth' : depth,
        'width' : width,
        'total_node_num' : total_node_num
    }
    return node_data

@app.route('/get_graph')
def get_graph():
    
    return render_template("graph.html")

@app.route('/get_graph_data')
def get_graph_data():
    graph_data = get_dependent_graph(commitments)
    print("graph_data = ",graph_data)
    return {"g_data": json.dumps(graph_data)}


tree_root = build_tree(commitments=commitments)
tree_data = get_tree_data()

with open('tree_data.json', 'w') as json_file:
    json_file.write(tree_data)
    
with open('tree_data.json', 'r') as json_file:
    # 解析 JSON 数据
    tree_data = json.load(json_file)
    

if __name__ == '__main__':
    app.run(host='127.0.0.1', port=5001,debug=True)