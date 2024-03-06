from enum import Enum
from collections import deque
import copy
from flask import Flask, render_template, jsonify,json,request
# from flask_sqlalchemy import SQLAlchemy
import json
import sys
import argparse

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
        self.sub_game_path = []

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
                    or_flag = False
                    and_opration = False
                    if commitments[i].Prerequisites == None:
                        child_node = TreeNode(commitments=copy.deepcopy(commitments_cp),parent=self)
                        child_node.player = player
                        self.children.append(child_node)
                        break
                    for key,value in commitments[i].Prerequisites.items():
                        dependent_state = None
                        if value[0] == 'sat':
                            dependent_state = CommitmentStatus.SAT
                        elif value[0] == 'exp':
                            dependent_state = CommitmentStatus.EXP
                        elif value[0] == 'vio':
                            dependent_state = CommitmentStatus.VIO
                        key = int(key) - 1
                        if value[1] == '&':
                            flag = flag and commitments[key].status == dependent_state
                            and_opration = True
                        elif value[1] == '|':
                            or_flag = or_flag or commitments[key].status == dependent_state
                    if and_opration:
                        flag = flag or or_flag
                    else:
                        flag = or_flag
                    if flag:                               
                        child_node = TreeNode(commitments=copy.deepcopy(commitments_cp),parent=self)
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
            r = values[3].split(',')
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
        
        result_dependent = list()
        if len(result) != 1:
            for i in range(1,len(result),1):
                result_dependent.append(result[i])
        result = result[0]
        self.result = result
        if result == '':
            self.result = None
        print("result = ",result," result_dependent = ",result_dependent)
        if result_dependent[0] == '':
            self.result_Prerequisites = None
        else:
            self.result_Prerequisites = {int(pair.split(':')[0]): pair.split(':')[1] for pair in result_dependent}
        # 时间，time是act_timeout,time_vio是vio_timeout,如果时间是无穷，则用-1表示
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
            self.Prerequisites = {int(pair.split(':')[0]): [pair.split(':')[1],pair.split(':')[2]] for pair in Prerequisites}
        # 承诺状态的最终收益
        if self.status == CommitmentStatus.SAT:
            if commitments[i].initiators[0] == "player1":
                commitments[i].finalpayoff = [-1*int(commitments[i].Allpayoff[0]),1*int(commitments[i].Allpayoff[1])]
            else:
                commitments[i].finalpayoff = [1*int(commitments[i].Allpayoff[0]),-1*int(commitments[i].Allpayoff[1])]
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
        print("commitment_data = ",commitment_data)
        commitments_init.append(Commitment(*commitment_data))
    return commitments_init


# 生成依赖图
def get_dependent_graph(commitments):
    dependent_graph = {}
    dependent_graph[0] = []
    for commitment in commitments:
        dependent_graph[int(commitment.commitment_id)] = []
        print("commitment.commitment_id = ",commitment.commitment_id)
        print("commitment.Prerequisites = ",commitment.Prerequisites)
        print("commitment.result_Prerequisites = ",commitment.result_Prerequisites)
    for commitment in commitments:
        if commitment.Prerequisites is None:
            continue
        for key, value in commitment.Prerequisites.items():
            dependent_graph[key].append((f"p.{key}.{value[0]}",int(commitment.commitment_id)))
    for commitment in commitments:
        if commitment.result_Prerequisites is None:
            continue
        for key,value in commitment.result_Prerequisites.items():
            dependent_graph[key].append((f"r.{key}.{value}",int(commitment.commitment_id)))
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


def change_state(node,player_commitments_index_status_time,BAS_position,bas_effect):
    print()
    print("----change_state_start----")
    print("player_commitments_index_status_time = ",player_commitments_index_status_time)
    commitments = node.commitments
    player = node.player
    final_status_queue = deque()
    final_status_set = (CommitmentStatus.SAT,CommitmentStatus.EXP,CommitmentStatus.VIO)
    # 如果有结果可以直接改变的承诺，优先改变这些承诺，再做后续判断
    for i in range(len(commitments)):
        if commitments[i].result_Prerequisites == None and commitments[i].result == 'null':
            final_status_queue.append(i)
    if bas_effect:
        # 初始化当前时间、备份当前承诺、改变当前承诺的状态
        cur_time = player_commitments_index_status_time[BAS_position][2]
        # 由于当前承诺状态改变而影响的承诺加入队列
        for infected_commitment_pr_index in dependent_graph[player_commitments_index_status_time[BAS_position][0]+1]:
            final_status_queue.append(infected_commitment_pr_index[1] - 1)
    else:
        cur_time = player_commitments_index_status_time[0][2]
        if commitments[player_commitments_index_status_time[0][0]].status == CommitmentStatus.ACT:
            commitments[player_commitments_index_status_time[0][0]].status = CommitmentStatus.EXP
        elif commitments[player_commitments_index_status_time[0][0]].status == CommitmentStatus.BAS:
            commitments[player_commitments_index_status_time[0][0]].status = CommitmentStatus.VIO
        for infected_commitment_pr_index in dependent_graph[player_commitments_index_status_time[0][0]+1]:
            final_status_queue.append(infected_commitment_pr_index[1] - 1)
        print("False final_status_queue = ",final_status_queue,"dependent_graph[player_commitments_index_status_time[0][0]+1] = ",dependent_graph[player_commitments_index_status_time[0][0]+1])
    print("final_status_queue = ",final_status_queue)
    while final_status_queue:
        # 由时间小于cur_time的承诺过期可能影响的承诺加入队列
        for i in range(len(commitments)):
            if commitments[i].status in final_status_set:
                continue
            if commitments[i].status == CommitmentStatus.ACT and commitments[i].time <= cur_time:
                commitments[i].status = CommitmentStatus.EXP
                for infected_commitment_pr_index in dependent_graph[i+1]:
                    final_status_queue.append(infected_commitment_pr_index[1]-1)
            elif commitments[i].status == CommitmentStatus.BAS and commitments[i].time_vio < cur_time:
                commitments[i].status = CommitmentStatus.VIO
                for infected_commitment_pr_index in dependent_graph[i+1]:
                    final_status_queue.append(infected_commitment_pr_index[1]-1)
        cur_C_index = final_status_queue.popleft()
        # 队头节点已经到达最终态的不做处理
        if commitments[cur_C_index].status in final_status_set:
            continue
        elif commitments[cur_C_index].status == CommitmentStatus.ACT:
            flag = True
            or_flag = False
            and_opration = False
            has_one_not_sat = False
            if commitments[cur_C_index].Prerequisites == None:
                commitments[cur_C_index].p = True
                commitments[cur_C_index].status = CommitmentStatus.BAS
                for key,value in commitments[cur_C_index].result_Prerequisites.items():
                    dependent_state = None
                    if value == 'sat':
                        dependent_state = CommitmentStatus.SAT
                    elif value == 'exp':
                        dependent_state = CommitmentStatus.EXP
                    elif value == 'vio':
                        dependent_state = CommitmentStatus.VIO
                    key = int(key) - 1
                    flag = flag and commitments[key].status == dependent_state
                    if commitments[key].status in final_status_set and commitments[key].status != dependent_state:
                        has_one_not_sat = True
                        break
                if flag:
                    commitments[cur_C_index].r = True
                    commitments[cur_C_index].status = CommitmentStatus.SAT
                    cur_time = commitments[cur_C_index].time_vio
                    for infected_commitment_pr_index in dependent_graph[cur_C_index + 1]:
                        print("flag = true cur_C_index = ",cur_C_index,"dependent_graph[cur_C_index + 1] = ",dependent_graph[cur_C_index + 1])
                        final_status_queue.append(infected_commitment_pr_index[1] - 1)
                else:
                    # 结果有一个不被满足，状态变成VIO，更新当前时间
                    if has_one_not_sat:
                        print("flag = False and has_one_not_sat = True cur_C_index = ",cur_C_index,"dependent_graph[cur_C_index + 1] = ",dependent_graph[cur_C_index + 1])
                        cur_time = commitments[cur_C_index].time_vio
                        commitments[cur_C_index].r = False
                        commitments[cur_C_index].status = CommitmentStatus.VIO
                        for infected_commitment_pr_index in dependent_graph[cur_C_index + 1]:
                            final_status_queue.append(infected_commitment_pr_index[1] - 1)
                continue
            for key,value in commitments[cur_C_index].Prerequisites.items():
                print("cur_C_index ____Prerequisites_value = ",value,"cur_C_index = ",cur_C_index)
                print("____commitments[key].status = ",commitments[key].status)
                dependent_state = None
                if value[0] == 'sat':
                    dependent_state = CommitmentStatus.SAT
                elif value[0] == 'exp':
                    dependent_state = CommitmentStatus.EXP
                elif value[0] == 'vio':
                    dependent_state = CommitmentStatus.VIO
                key = int(key) - 1
                if value[1] == '&':
                    flag = flag and commitments[key].status == dependent_state
                    and_opration = True
                    if commitments[key].status in final_status_set and commitments[key].status != dependent_state:
                        has_one_not_sat = True
                        break
                elif value[1] == '|':
                    if commitments[key].status not in final_status_set:
                        has_one_not_sat = False
                        break
                    or_flag = or_flag or commitments[key].status == dependent_state
            if and_opration:
                flag = flag or or_flag
            else:
                flag = or_flag
            print("____cur_C_index = ",cur_C_index,"flag = ",flag)
            # 前提条件全部满足，变成就绪态
            if flag:
                commitments[cur_C_index].p = True
                commitments[cur_C_index].status = CommitmentStatus.BAS
                if commitments[cur_C_index].result != 'null':
                    continue
                # 判断能不能直接到达最终态，并考虑把收到影响的承诺加入队列
                if commitments[cur_C_index].result_Prerequisites == None and commitments[cur_C_index].result == 'null':
                    commitments[cur_C_index].status = CommitmentStatus.SAT
                    continue
                for key,value in commitments[cur_C_index].result_Prerequisites.items():
                    dependent_state = None
                    if value == 'sat':
                        dependent_state = CommitmentStatus.SAT
                    elif value == 'exp':
                        dependent_state = CommitmentStatus.EXP
                    elif value == 'vio':
                        dependent_state = CommitmentStatus.VIO
                    key = int(key) - 1
                    flag = flag and commitments[key].status == dependent_state
                    if commitments[key].status in final_status_set and commitments[key].status != dependent_state:
                        has_one_not_sat = True
                        break
                if flag:
                    commitments[cur_C_index].r = True
                    commitments[cur_C_index].status = CommitmentStatus.SAT
                    cur_time = commitments[cur_C_index].time_vio
                    for infected_commitment_pr_index in dependent_graph[cur_C_index + 1]:
                        print("flag = true cur_C_index = ",cur_C_index,"dependent_graph[cur_C_index + 1] = ",dependent_graph[cur_C_index + 1])
                        final_status_queue.append(infected_commitment_pr_index[1] - 1)
                else:
                    # 结果有一个不被满足，状态变成VIO，更新当前时间
                    if has_one_not_sat:
                        print("flag = False and has_one_not_sat = True cur_C_index = ",cur_C_index,"dependent_graph[cur_C_index + 1] = ",dependent_graph[cur_C_index + 1])
                        cur_time = commitments[cur_C_index].time_vio
                        commitments[cur_C_index].r = False
                        commitments[cur_C_index].status = CommitmentStatus.VIO
                        for infected_commitment_pr_index in dependent_graph[cur_C_index + 1]:
                            final_status_queue.append(infected_commitment_pr_index[1] - 1)
            else:
                # 前提条件有一个不满足，变成过期态，更新当前时间
                if has_one_not_sat:
                    cur_time = commitments[cur_C_index].time
                    commitments[cur_C_index].p = False
                    commitments[cur_C_index].status = CommitmentStatus.EXP
                    for infected_commitment_pr_index in dependent_graph[cur_C_index + 1]:
                        final_status_queue.append(infected_commitment_pr_index[1] - 1)
                # 前提条件可能被满足，不做处理
                else:
                    pass
        elif commitments[cur_C_index].status == CommitmentStatus.BAS:
            print("commitments.status = ",[e.status.value for e in commitments])
            print("commitments[cur_C_index].status == CommitmentStatus.BAS cur_C_index = ",cur_C_index,"commitments[cur_C_index].result = ",commitments[cur_C_index].result,"commitments[cur_C_index].result_Prerequisites = ",commitments[cur_C_index].result_Prerequisites)
            flag = True
            has_one_not_sat = False
            # 如果r中仅有承诺依赖时可以直接变成SAT，否则会分裂成两个节点，这里不能改变，要加一个条件：真实动作为空
            if commitments[cur_C_index].result_Prerequisites == None and commitments[cur_C_index].result == 'null':
                commitments[cur_C_index].status = CommitmentStatus.SAT
                commitments[cur_C_index].r = True
                cur_time = commitments[cur_C_index].time_vio
                for infected_commitment_pr_index in dependent_graph[cur_C_index + 1]:
                    final_status_queue.append(infected_commitment_pr_index[1] - 1)
                continue
            if commitments[cur_C_index].result == 'null':
                print(f"cur_C_index = {cur_C_index}commitments[cur_C_index].result == 'null',commitments[cur_C_index].result_Prerequisites = {commitments[cur_C_index].result_Prerequisites}")
                for key,value in commitments[cur_C_index].result_Prerequisites.items():
                    dependent_state = None
                    if value == 'sat':
                        dependent_state = CommitmentStatus.SAT
                    elif value == 'exp':
                        dependent_state = CommitmentStatus.EXP
                    elif value == 'vio':
                        dependent_state = CommitmentStatus.VIO
                    key = int(key) - 1
                    flag = flag and commitments[key].status == dependent_state
                    if commitments[key].status in final_status_set and commitments[key].status != dependent_state:
                        has_one_not_sat = True
                        break
                    
                print("cur_C_index = ",cur_C_index,"flag = ",flag,"has_one_not_sat = ",has_one_not_sat)
                # 结果依赖全都被满足，状态变成SAT，更新当前时间
                if flag:
                    commitments[cur_C_index].r = True
                    commitments[cur_C_index].status = CommitmentStatus.SAT
                    cur_time = commitments[cur_C_index].time_vio
                    for infected_commitment_pr_index in dependent_graph[cur_C_index + 1]:
                        print("flag = true cur_C_index = ",cur_C_index,"dependent_graph[cur_C_index + 1] = ",dependent_graph[cur_C_index + 1])
                        final_status_queue.append(infected_commitment_pr_index[1] - 1)
                else:
                    # 结果有一个不被满足，状态变成VIO，更新当前时间
                    if has_one_not_sat:
                        print("flag = False and has_one_not_sat = True cur_C_index = ",cur_C_index,"dependent_graph[cur_C_index + 1] = ",dependent_graph[cur_C_index + 1])
                        cur_time = commitments[cur_C_index].time_vio
                        commitments[cur_C_index].r = False
                        commitments[cur_C_index].status = CommitmentStatus.VIO
                        for infected_commitment_pr_index in dependent_graph[cur_C_index + 1]:
                            final_status_queue.append(infected_commitment_pr_index[1] - 1)
                    # 结果有真实事件/有一个依赖可能被满足，不做处理
                    else:
                        pass
    new_node = TreeNode(commitments=copy.deepcopy(commitments),parent=node.parent)
    new_node.player = player
    print("node commitments = ",[e.status.value for e in new_node.commitments],"player = ",new_node.player)
    print("----change_state_end----")
    print()
    return new_node
    

# 返回当前节点玩家的孩子节点
# 当前节点只能有一个玩家做动作
# 只有结果事件中有真实动作的才会分裂成多个节点，否则直接改变至最终状态
def get_child(node):
    # 初始化
    global dependent_graph
    player_child_node_list = list()
    player_commitments_index_status_time = list()
    player = node.player
    commitments = node.commitments
    BAS_position = 0
    bas_effect = False
    result_dependent_is_sat = False
    print()
    print(f"----get_child----start----commitments = {[e.status.value for e in node.commitments]},player = {node.player}")
    # 按时间排序生成当前玩家承诺的有序列表
    for i in range(len(commitments)):
        if commitments[i].status in (CommitmentStatus.SAT,CommitmentStatus.EXP,CommitmentStatus.VIO):
            continue
        if commitments[i].initiators[0] == player and commitments[i].status == CommitmentStatus.ACT:
            player_commitments_index_status_time.append((i,commitments[i].status,commitments[i].time))
        elif commitments[i].initiators[0] == player and commitments[i].status == CommitmentStatus.BAS:
            player_commitments_index_status_time.append((i,commitments[i].status,commitments[i].time_vio))
    player_commitments_index_status_time = sorted(player_commitments_index_status_time,key=lambda x:x[2])
    print("player_commitments_index_status_time = ",player_commitments_index_status_time)
    # 判断当前玩家是否存在就绪态承诺，如果存在，则生成两个节点：sat和vio，如果不存在，则生成一个节点exp
    print(f"commitments[player_commitments_index_status_time[0][0]].result = {commitments[player_commitments_index_status_time[0][0]].result}")
    has_bas_status = False
    for index,status,time in player_commitments_index_status_time:
        print(f"____index = {index},status = {status.value},time = {time},commitments[index].status = {commitments[index].status},commitments[index].result = {commitments[index].result}____")
        if commitments[index].status == CommitmentStatus.BAS:
            has_bas_status = True
            flag = True
            # 结果事件不为空时 表明有真实动作 此时bas_effect = True 否则直接原地修改状态
            if commitments[index].result != 'null':
                if commitments[index].result_Prerequisites == None:
                    bas_effect = True
                    break
                for key,value in commitments[index].result_Prerequisites.items():
                    if key == 0:
                        continue
                    print("index = ",index,"commitments[index].result_Prerequisites.items() = ",commitments[index].result_Prerequisites.items())
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
                    bas_effect = True
                    break
        BAS_position += 1
    print("BAS_position = ",BAS_position,"bas_effect = ",bas_effect,"has_bas_status = ",has_bas_status)
    # 只要有BAS状态而且result中有真实动作，就要生成两个节点，这里少一个判断逻辑
    if bas_effect:
        print("____bas_effect = True____")
        sat_child_node = TreeNode(commitments=commitments)
        sat_child_node.commitments[player_commitments_index_status_time[BAS_position][0]].status = CommitmentStatus.SAT
        print("sat_child_node before change state = ",[e.status.value for e in sat_child_node.commitments])
        sat_child_node = change_state(node=copy.deepcopy(sat_child_node),player_commitments_index_status_time=player_commitments_index_status_time,BAS_position=BAS_position,bas_effect=bas_effect)
        print("sat_child_node after change state = ",[e.status.value for e in sat_child_node.commitments])
        player_child_node_list.append(sat_child_node)
        # 这里的commitment加一个tag，如果tag成立就跳过生成vio节点，result_Prerequisites[key]==0时代表一定执行成功
        must_executed = False
        if commitments[player_commitments_index_status_time[BAS_position][0]].result_Prerequisites:
            for key,value in commitments[player_commitments_index_status_time[BAS_position][0]].result_Prerequisites.items():
                if key == 0 and value == 'sat':
                    must_executed = True
        if not must_executed:
            print("must_executed = ",must_executed)
            vio_child_node = TreeNode(commitments=commitments)
            vio_child_node.commitments[player_commitments_index_status_time[BAS_position][0]].status = CommitmentStatus.VIO
            print("vio_child_node before change state = ",[e.status.value for e in vio_child_node.commitments])
            vio_child_node = change_state(node=vio_child_node,player_commitments_index_status_time=player_commitments_index_status_time,BAS_position=BAS_position,bas_effect=bas_effect)
            print("vio_child_node after change state = ",[e.status.value for e in vio_child_node.commitments])
            player_child_node_list.append(vio_child_node)
    else:
        # 当前玩家没有bas状态的承诺，只能使某个承诺过期
        if not has_bas_status:
            exp_child_node = change_state(node=node,player_commitments_index_status_time=player_commitments_index_status_time,BAS_position=BAS_position,bas_effect=bas_effect)
            player_child_node_list.append(exp_child_node)
        # 当前玩家有bas状态的承诺，但是没有真实事件，不应该分裂成两个节点，直接原地修改状态
        # 原地修改后的节点承诺中如果还有玩家可以做动作，则变更节点的玩家归属，并判断是否分裂
        else:
            print("----get_child_end return none----")
            return None
    # 存在就绪态承诺
    # ---------------------------原代码-------------------------
    # player_child_node_list = list()
    # player_commitments_index = list()
    # commitments = node.commitments
    # player = node.player
    # # 找出发出者是玩家1和玩家2的承诺索引和状态（index，status）
    # # 通过承诺的timeout时间对状态排序，如果当前顺序中存在状态为BAS的承诺，则会分裂出多个节点
    # # 根据BAS->SAT的可能时间生成树中某一层的节点
    # for i in range(len(commitments)):
    #     if commitments[i].status in (CommitmentStatus.SAT,CommitmentStatus.EXP,CommitmentStatus.VIO):
    #         continue
    #     # 分别获取player1和player2的未到最终态的承诺索引
    #     if commitments[i].initiators[0] == player:
    #         player_commitments_index.append(i)
    # player_child_node_list = get_player_child_list(node = copy.deepcopy(node),player_commitments_index = player_commitments_index)      
    # ------------------------原代码-------------------------
    # player1_action_index_status_time = sorted(player1_action_index_status_time,key = lambda x:x[2])
    # player2_action_index_status_time = sorted(player2_action_index_status_time,key = lambda x:x[2])
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
    print("----get_child_end----")
    print()
    for node in player_child_node_list:
        print("get child return player_child_node = ",[e.status.value for e in node.commitments])
    print("get child return")
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
            if value[0] == 'sat':
                dependent_state = CommitmentStatus.SAT
            elif value[0] == 'exp':
                dependent_state = CommitmentStatus.EXP
            elif value[0] == 'vio':
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
            and_opration = False
            or_flag = False
            for key,value in commitments[i].Prerequisites.items():
                dependent_state = None
                if value[0] == 'sat':
                    dependent_state = CommitmentStatus.SAT
                elif value[0] == 'exp':
                    dependent_state = CommitmentStatus.EXP
                elif value[0] == 'vio':
                    dependent_state = CommitmentStatus.VIO
                key = int(key) - 1
                if value[1] == '&':
                    flag = flag and commitments[key].status == dependent_state
                    and_opration = True
                elif value[1] == '|':
                    or_flag = or_flag or commitments[key].status == dependent_state
            if and_opration:
                flag = flag or or_flag
            else:
                flag = or_flag
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
            if value[0] == 'sat':
                dependent_state = CommitmentStatus.SAT
            elif value[0] == 'exp':
                dependent_state = CommitmentStatus.EXP
            elif value[0] == 'vio':
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
            if commitments[i].initiators[0] == "player1":
                commitments[i].finalpayoff = [-1*int(commitments[i].Allpayoff[0]),1*int(commitments[i].Allpayoff[1])]
            else:
                commitments[i].finalpayoff = [1*int(commitments[i].Allpayoff[0]),-1*int(commitments[i].Allpayoff[1])]
            print("i = ",i,"commitments[i].finalpayoff = ",commitments[i].finalpayoff)
        elif commitments[i].status == CommitmentStatus.EXP:
            commitments[i].finalpayoff = [0,0]
        elif commitments[i].status == CommitmentStatus.VIO:
            commitments[i].finalpayoff = [0,0]
    for i in range(len(commitments)):
        if commitments[i].status not in (CommitmentStatus.EXP,CommitmentStatus.VIO,CommitmentStatus.SAT):
            position = i -1
            break
    if flag:
        return True,commitments,position
    else:
        return False,commitments,position


def player_has_actions(commitments,player):
    # print("____player_has_actions____START")
    # print("player_has_actions commitments[i].status = ",[e.status.value for e in commitments],"player = ",player)
    for i in range(len(commitments)):
        if commitments[i].status in (CommitmentStatus.EXP,CommitmentStatus.VIO,CommitmentStatus.SAT):
            # print("Continue: commitment_id = ",i+1,"commitments[i].status = ",commitments[i].status.value)
            continue
        if commitments[i].initiators[0] == player and commitments[i].status == CommitmentStatus.BAS:
            # print("player has bas status commitments[i].status = ",[e.status.value for e in commitments],"player = ",player)
            return True
    # print("player doesn't has bas status commitments[i].status = ",[e.status.value for e in commitments],"player = ",player)
    # print("____player_has_actions____END")
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
    pop = 0
    while queue:
        pop += 1
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
        print("____cur_node_status = ",[e.status.value for e in cur_node.commitments])
        cur_node_children = get_child(copy.deepcopy(cur_node))
        for cur_node_child in cur_node_children:
            print("____cur_node_child_commitments status = ",[e.status.value for e in cur_node_child.commitments])
        # 如果当前节点的玩家没有真实动作，则不应该分裂成两个节点，直接原地修改当前节点
        if cur_node_children == None:
            player_commitments_index_status_time = list()
            BAS_position = 0
            bas_effect = False
            for i in range(len(commitments)):
                if commitments[i].status in (CommitmentStatus.SAT,CommitmentStatus.EXP,CommitmentStatus.VIO):
                    continue
                if commitments[i].initiators[0] == cur_node.player and commitments[i].status == CommitmentStatus.ACT:
                    player_commitments_index_status_time.append((i,commitments[i].status,commitments[i].time))
                elif commitments[i].initiators[0] == cur_node.player and commitments[i].status == CommitmentStatus.BAS:
                    player_commitments_index_status_time.append((i,commitments[i].status,commitments[i].time_vio))
            player_commitments_index_status_time = sorted(player_commitments_index_status_time,key=lambda x:x[2])
            
            for index,status,time in player_commitments_index_status_time:
                if commitments[index].status == CommitmentStatus.BAS:
                    bas_effect = True
                    break
                BAS_position += 1
            print("before cur_node_temp change_state: cur_node_temp.commitments = ",[e.status.value for e in cur_node.commitments])
            cur_node_temp = change_state(node=cur_node,player_commitments_index_status_time=player_commitments_index_status_time,BAS_position=BAS_position,bas_effect=bas_effect)
            print("after cur_node_temp change_state: cur_node_temp.commitments = ",[e.status.value for e in cur_node.commitments])
            isfinal,payoff_commitments,position = is_final(copy.deepcopy(cur_node_temp.commitments))
            # 如果当前节点的所有承诺全都到达了最终态，计算收益
            if isfinal:
                player1_payoff = 0
                player2_payoff = 0
                for commitment in payoff_commitments:
                    player1_payoff += commitment.finalpayoff[0]
                    player2_payoff += commitment.finalpayoff[1]
                cur_node.commitments = payoff_commitments
                cur_node.payoff = (player1_payoff,player2_payoff)
            # 否则，判断当前节点的玩家归属，如果有多个玩家，就分裂成多个节点加入队列
            else:
                left_players = set()
                for i in range(len(cur_node.commitments)):
                    if cur_node.commitments[i].status in (CommitmentStatus.EXP,CommitmentStatus.VIO,CommitmentStatus.SAT):
                        continue
                    if cur_node.commitments[i].initiators[0] not in left_players:
                        left_players.add(cur_node.commitments[i].initiators[0])
                for player in left_players:
                    new_node = copy.deepcopy(cur_node)
                    new_node.player = player
                    new_node.parent = cur_node.parent
                    queue.append(new_node)
            continue
        for cur_node_child in cur_node_children:
            cur_node_child.player = cur_node.player
            cur_node_child.parent = cur_node
            isfinal,payoff_commitments,position = is_final(copy.deepcopy(cur_node_child.commitments))
            if isfinal:
                player1_payoff = 0
                player2_payoff = 0
                for commitment in payoff_commitments:
                    player1_payoff += commitment.finalpayoff[0]
                    player2_payoff += commitment.finalpayoff[1]
                cur_node_child.commitments = payoff_commitments
                cur_node_child.payoff = (player1_payoff,player2_payoff)
                cur_node.add_child(cur_node_child)
                print("----build_tree---- cur_node_child.payoff = ",cur_node_child.payoff,"cur_node_child.commitments = ",[e.status.value for e in cur_node_child.commitments],"player = ",cur_node_child.player)
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

def find_sub_tree_max_payoff(node):
    print("----find_sub_tree_max_payoff-START----")
    children = node.children
    for child in children:
        print("child_commitemnts = ",[e.status.value for e in child.commitments])
    player = node.player
    print("player = ",player)
    max_index = 0
    sub_EQ = None
    if player == "player1":
        for i in range(len(children)):
            print("____i = ",i,"children[i] = ",children[i],"children[i].payoff = ",children[i].payoff)
            if children[i].payoff[0] >= children[max_index].payoff[0]:
                max_index = i 
                sub_EQ = children[max_index].payoff
        print("player1 sub_EQ = ",sub_EQ)
    elif player == "player2":
        for i in range(len(children)):
            print("player2 child commitments = ",[e.status.value for e in children[i].commitments],"player = ",children[i].player,"payoff = ",children[i].payoff)
            if children[i].children:
                for child in children[i].children:
                    print("child.payoff = ",child.payoff,"child.commitments = ",[e.status.value for e in child.commitments],"player = ",child.player)
            print("____i = ",i,"children[i] = ",children[i],"children[i].payoff = ",children[i].payoff)
            if children[i].payoff[1] >= children[max_index].payoff[1]:
                max_index = i 
                sub_EQ = children[max_index].payoff
        print("player2 sub_EQ = ",sub_EQ)
    else:
        print("player error!")
    node.children[max_index].payoff = sub_EQ
    print("node.children[max_index].payoff = ",node.children[max_index].payoff)
    print("----find_sub_tree_max_payoff-END----")
    return node.children[max_index]


# 非递归，双栈后序遍历博弈树，计算子subEQ，每一个节点都保存路径
def postorder_traversal(root):
    print("----postorder_traversal----Start")
    if not root:
        return []

    Node_Stack = [root]  # 用于保存节点
    Result_Stack = []  # 用于保存遍历结果

    while Node_Stack:
        node = Node_Stack.pop()
        Result_Stack.append(node)

        for child in node.children:
            Node_Stack.append(child)

    while Result_Stack:
        if not Result_Stack[-1].children:
            Result_Stack.pop()
            continue

        cur_node = Result_Stack.pop()
        print("post_order_traversal cur_node.commitments = ",[e.status.value for e in cur_node.commitments],"payoff = ",cur_node.payoff,"player = ",cur_node.player)
        if cur_node.children:
            for child in cur_node.children:
                print("post order traversal cur_node.child.commitments = ",[e.status.value for e in child.commitments],"pay off = ",child.payoff)
        # 如果是根节点，没有player属性，无法判断孩子节点的max_payoff，所有孩子的path都append进根节点的path，然后返回
        if cur_node.player == "root":
            for child in cur_node.children:
                cur_node.sub_game_path.append(child.sub_game_path)
            return cur_node
        
        sub_EQ_node = find_sub_tree_max_payoff(cur_node)
        cur_node.sub_game_path.append(cur_node)
        cur_node.payoff = sub_EQ_node.payoff
        if not sub_EQ_node.sub_game_path:
            cur_node.sub_game_path.append(sub_EQ_node)
        else:
            for sub_game_path_node in sub_EQ_node.sub_game_path:
                cur_node.sub_game_path.append(sub_game_path_node)
    print("----postorder_traversal----End")
    return root


# file_path = "real_contract.txt"
# commitments_data = parse_commitment_file(file_path)
# print("commitment_data = ",commitments_data)
# commitments = get_commitments(commitments_data)


    
# dependent_graph = get_dependent_graph(commitments)
# print(dependent_graph)
# try:
#     sorted_result = topological_sort(dependent_graph,commitments)
#     print("Topological Sort Result:", sorted_result)
# except ValueError as e:
#     print(f"Error: {e}")
# print("dependent graph = ",dependent_graph)
# tree_root = build_tree(commitments=commitments)

    
# depth,width,total_node_num = tree_properties(tree_root)

# final_node = postorder_traversal(tree_root)
# print("final node = ",final_node)
# for node in final_node.sub_game_path:
#     print("final_node = ",[e.status.value for e in node.commitments])

# for node_list in final_node.sub_game_path:
#     for node in node_list:
#         print("final_node = ",[e.status.value for e in node.commitments])


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


# tree_root = build_tree(commitments=commitments)
# tree_data = get_tree_data()

# with open('tree_data.json', 'w') as json_file:
#     json_file.write(tree_data)
    
# with open('tree_data.json', 'r') as json_file:
#     # 解析 JSON 数据
#     tree_data = json.load(json_file)


def parse_arguments():
    parser = argparse.ArgumentParser(description='Run the Flask app with optional file path argument.')
    parser.add_argument('-u', '--file_path', help='Path to the file to be processed.')

    return parser.parse_args()

if __name__ == '__main__':
    args = parse_arguments()
    print("args = ",args.file_path)
    file_path = args.file_path
    commitments_data = parse_commitment_file(file_path)
    print("commitment_data = ",commitments_data)
    commitments = get_commitments(commitments_data)
    for commitment in commitments:
        print("All pay off = ",commitment.Allpayoff)
    dependent_graph = get_dependent_graph(commitments)
    tree_root = build_tree(commitments=commitments)
    depth,width,total_node_num = tree_properties(tree_root)
    final_node = postorder_traversal(tree_root)
    print("final node = ",final_node,"len = ",len(final_node.sub_game_path))
    if len(final_node.sub_game_path) > 1:
        for nodes in final_node.sub_game_path:
            for node in nodes:
                print("final_node = ",[e.status.value for e in node.commitments])
    else:
        for node in final_node.sub_game_path:
            print("final_node = ",[e.status.value for e in node.commitments])
    app.run(host='127.0.0.1', port=5001,debug=True)