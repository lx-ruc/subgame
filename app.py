from enum import Enum
from collections import deque
import copy
from flask import Flask, render_template, jsonify,json,request
from flask_sqlalchemy import SQLAlchemy
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
    def __init__(self, commitments, parent=None):
        self.commitments = commitments
        self.children = []
        self.parent = parent
        self.player = None

    def add_child(self, child):
        self.children.append(child)
        
    def init(self,parent = None):
        for i in range(len(self.commitments)):
            self.commitments[i].status = CommitmentStatus.ACT
            self.commitments[i].p = False
            self.commitments[i].r = False
            self.commitments[i].tc = False
            
    # 打印树的结构
    def __str__(self, level=0):
        status = list()
        for term in self.commitments:
            status.append(term.status)
        ret = "\t" * level + f"{[e for e in status]}" + "\n"+"\n"
        for child in self.children:
            ret += child.__str__(level + 1)
        return ret
    
    
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
            time = int(values[4])
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
        print("Prerequisites= ",Prerequisites)
        # 结果
        self.r = False
        self.result = result
        # 时间
        self.time = time
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

        
            
            

def get_commitments(commitments_data):
    commitments_init = []
    for commitment_data in commitments_data:
        commitments_init.append(Commitment(*commitment_data))
    return commitments_init

        
def get_dependent_graph(commitments):
    dependent_graph = {}
    for commitment in commitments:
        temp_list = list()
        if commitment.Prerequisites == None:
            continue
        for key,value in commitment.Prerequisites.items():
            temp_list.append(f"{key}.{value}")
        dependent_graph[commitment.commitment_id] = temp_list
    return dependent_graph


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


# 返回当前节点的孩子节点，分成player1-playern
def get_child(commitments,player):
    player1_child_node_list = list()
    player2_child_node_list = list()
    player1_action_index_status_time = list()
    player2_action_index_status_time = list()
    # 找出发出者是玩家1和玩家2的承诺索引和状态（index，status）
    # 通过承诺的timeout时间对状态排序，如果当前顺序中存在状态为BAS的承诺，则会分裂出多个节点
    # 根据BAS->SAT的可能时间生成树中某一层的节点
    for i in range(len(commitments)):
        if commitments[i].initiators == "player1":
            player1_action_index.append((i,commitments[i].status,commitments[i].time))
        elif commitments[i].initiators == "player2":
            player2_action_index.append((i,commitments[i].status,commitments[i].time))
    player1_action_index_status_time = sorted(player1_action_index_status_time,key = lambda x:x[2])
    player2_action_index_status_time = sorted(player2_action_index_status_time,key = lambda x:x[2])
    
            
    for i in range(len(commitments)):
        # 当前承诺的状态是最终态，直接跳过
        if commitments[i].status in (CommitmentStatus.EXP,CommitmentStatus.VIO,CommitmentStatus.SAT):
            continue
        # 承诺状态是激活态，依赖的承诺状态符合前提条件，直接转变为就绪态
        # 就绪态会产生两个分支：sat和vio，传入change_satate确定孩子节点的最终状态
        elif commitments[i].status == CommitmentStatus.BAS:
            commitments[i].status = CommitmentStatus.SAT
            sat_commitments = commitments
            child_node_list.append(change_state(copy.deepcopy(sat_commitments)))
            commitments[i].status = CommitmentStatus.VIO
            vio_commitments = commitments
            child_node_list.append(change_state(copy.deepcopy(vio_commitments)))
    return child_node_list

# 传入某个player的action_list三元组，返回这个player的所有孩子节点
def get_player_child_list(commitments,action_index_status_time):
    commitments = copy.deepcopy(commitments)
    child_node_list = list()
    BAS_list = list()
    BAS_position = 0
    for index,status,time in action_index_status_time:
        BAS_position += 1
        if status == CommitmentStatus.BAS:
            BAS_list.append(index)
            break
    # 假设只有一个BAS状态，获取BAS的位置，模拟在不同时间变成SAT
    # 由于BAS一定会转变为SAT，先把最早变成SAT的节点加入到child_node_list中
    BAS_index = BAS_index[0]
    child_node_list.append(commitments)
    for i in range(1,BAS_position + 1,1):
        if action_index_status_time[i][1] == CommitmentStatus.ACT:
            
            
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
    
def init_root_child(root):
    commitments = root.commitments
    players = set()
    for commitment in commitments:
        if commitment.initiators not in players:
            players.add(initiators)
    for player in players:
        for i in range(len(commitments)):
            if commitments[i].
            
        root_child = TreeNode(commitments=commitments)
        rood.add_child(root_child)
        
    return root
# 构建博弈树
# 初始化一个全是ACT状态的根节点，然后分裂成各玩家的状态节点
def build_tree(commitments):
    root = TreeNode(commitments=commitments,parent=None)
    queue = deque([root.init()])
    while queue:
        cur_node = queue.popleft()
        result_commitments_list = get_child(copy.deepcopy(cur_node.commitments),player)
        for result_commitments in result_commitments_list:
            # 如果是最终态，不需要生成新的分支，不入队,直接给出收益
            isfinal,payoff_commitments,position = is_final(copy.deepcopy(result_commitments))
            if isfinal:
                cur_node.add_child(TreeNode(commitments=payoff_commitments,parent=cur_node))
            # 如果不是最终态，入队
            else:
                child = TreeNode(commitments=payoff_commitments,parent=cur_node)
                cur_node.add_child(child)
                queue.append(child)
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

file_path = "./commitment_file.txt"
commitments_data = parse_commitment_file(file_path)
print("commitments_data = ",commitments_data)
commitments = get_commitments(commitments_data)

# for commimet in commitments:
#     print(commimet.__dict__)
    
dependent_graph = get_dependent_graph(commitments)
# print("dependent graph = ",dependent_graph)
tree_root = build_tree(commitments=commitments)
print()
print(tree_root)

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
        'children': [convert_tree_to_dict(child) for child in node.children]
    }
    return node_data


tree_root = build_tree(commitments=commitments)
tree_data = get_tree_data()

with open('tree_data.json', 'w') as json_file:
    json_file.write(tree_data)
    
with open('tree_data.json', 'r') as json_file:
    # 解析 JSON 数据
    tree_data = json.load(json_file)
    

if __name__ == '__main__':
    app.run(debug=True)