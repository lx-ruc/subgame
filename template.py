from enum import Enum
import pygambit as gbt

class CommitmentStatus(Enum):
    ACT = 1
    BAS = 2
    SAT = 3
    EXP = 4
    VIO = 5

# 博弈树节点信息：承诺：commitment，孩子节点列表：children，父节点：parent
class CommitmentTreeNode:
    def __init__(self, commitment, parent=None):
        self.commitment = commitment
        self.children = []
        self.parent = parent

    def add_child(self, child):
        self.children.append(child)
    
    # 打印树的结构
    def __str__(self, level=0):
        ret = "\t" * level + repr(self.commitment.status) + "\n"
        for child in self.children:
            ret += child.__str__(level + 1)
        return ret

# 承诺类，仅用于初始化，后续的状态转移用因果图实现
class Commitment:
    def __init__(self, commitment_id, initiators, receivers, p,Prerequisites, r,result, tc, status=CommitmentStatus.ACT):
        # 承诺id
        self.commitment_id = commitment_id
        # 动作发出者（可能是多个）
        self.initiators = initiators
        # 动作接受者（可能是多个）
        self.receivers = receivers
        # 三个布尔变量用于确定当前承诺的状态
        # 前提条件
        self.p = p
        self.Prerequisites = Prerequisites
        # 结果
        self.r = r
        self.result = result
        # 时间
        self.tc = tc
        self.time = time
        self.status = status
        self.dependencies = []

    def fulfill_commitment(self):
        if self.status == CommitmentStatus.ACT:
            # 当前承诺的状态为ACT，且tc=true，依赖承诺的状态可以满足前提p，则状态转变为BAS，前提p=true
            if not self.p or any(dep.status not in [CommitmentStatus.EXP, CommitmentStatus.SAT, CommitmentStatus.VIO] for dep in self.dependencies):
                self.status = CommitmentStatus.BAS
                return "承诺状态变为BAS"

        elif self.status == CommitmentStatus.BAS:
            self.p = True
            # 产生两个分支
            sat_commitment = Commitment(self.commitment_id, self.initiators, self.receivers, self.p, self.r, self.tc, CommitmentStatus.SAT)
            vio_commitment = Commitment(self.commitment_id, self.initiators, self.receivers, self.p, self.r, self.tc, CommitmentStatus.VIO)
            
            # 添加两个分支到依赖
            self.dependencies.append(sat_commitment)
            self.dependencies.append(vio_commitment)

            return "承诺产生两个分支：SAT 和 VIO"

        return "无状态变化"

    def is_within_deadline(self):
        return self.tc > 0

class CommitmentTree:
    def __init__(self):
        self.root = None

    def build_tree(self, commitment, parent=None):
        node = CommitmentTreeNode(commitment, parent)
        for dep in commitment.dependencies:
            node.add_child(self.build_tree(dep, node))
        return node

    def display_tree(self):
        if self.root:
            print(self.root)

def parse_commitment_file(file_path):
    commitments = []
    with open(file_path, 'r', encoding='utf-8') as file:
        for line in file:
            values = line.strip().split(';')
            commitment_id = str(len(commitments) + 1)
            initiators = values[0].split(',')
            receivers = values[1].split(',')
            p = values[2]
            r = values[3]
            tc = int(values[4])
            dependent_on = values[5].split(';') if len(values) > 5 else None
            dependency_status = [CommitmentStatus(int(status)) for status in values[6].split(',')] if len(values) > 6 else None
            status = CommitmentStatus.ACT if not dependent_on or any(dep_status == CommitmentStatus.ACT for dep_status in dependency_status) else CommitmentStatus.BAS
            commitments.append((commitment_id, initiators, receivers, p, r, tc, dependent_on, dependency_status, status))
    return commitments

g = gbt.Game.read_game("./spence.efg")
results = gbt.nash.enumpure_solve(g,False,False)
for result in results:
    print("result = ",result)