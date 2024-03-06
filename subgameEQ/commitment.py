class Commitment:
    def __init__(self, initiators, receivers, p, r, tc):
        self.initiators = initiators
        self.receivers = receivers
        self.p = p
        self.r = r
        self.tc = tc
        self.status = "act"

    def fulfill_commitment(self):
        if self.status == "act" and self.p and self.is_within_deadline():
            self.status = "bas"
            return "承诺已激活，前提条件为真。等待结果。"

        elif self.status == "bas" and self.is_within_deadline():
            return "承诺就绪。等待结果。"

        elif self.status == "act" and not self.is_within_deadline():
            self.status = "exp"
            return "承诺已过期。超出时间限制。"

        elif self.status == "bas" and self.p and self.is_within_deadline():
            self.status = "sat"
            self.r = True
            return f"承诺已满足：{self.r}"

        elif self.status == "bas" and not self.is_within_deadline():
            self.status = "vio"
            return "承诺违约：超出时间限制。"
        else:
            return "无效的状态转换。"

    def is_within_deadline(self):
        return self.tc > 0

# 承诺因果关系图
class CommitmentGraph:
    def __init__(self):
        self.commitments = {}
        self.dependencies = {}

    def add_commitment(self, commitment_id, initiators, receivers, p, r, tc, dependent_on=None):
        new_commitment = Commitment(initiators, receivers, p, r, tc)
        self.commitments[commitment_id] = new_commitment

        if dependent_on:
            self.dependencies[commitment_id] = dependent_on

    def fulfill_commitment(self, commitment_id):
        current_commitment = self.commitments.get(commitment_id)

        if current_commitment:
            if commitment_id in self.dependencies:
                dependency_ids = self.dependencies[commitment_id]
                for dependency_id in dependency_ids:
                    self.fulfill_commitment(dependency_id)

            result = current_commitment.fulfill_commitment()
            return f"承诺 {commitment_id}：{result}"
        else:
            return f"找不到承诺 {commitment_id}。"

# 文件结构：
# 动作发出者1，动作发出者n；动作接受者1，动作接受者n；前提依赖1：状态，前提依赖n：状态；结果事件1，结果事件n；完成所需时间
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
            commitments.append((commitment_id, initiators, receivers, p, r, tc, dependent_on))
    return commitments


# 读取承诺文件
file_path = "./commitment"
graph = CommitmentGraph()


# 读取并显示文件内容
with open(file_path, 'r', encoding='utf-8') as file:
    file_content = file.read()
    print("文件内容：")
    print(file_content)


# 解析文件并添加承诺及依赖关系到图中
# 返回一个列表commitment[（发出者，接受者，前提条件，结果，时间）]
commitments_data = parse_commitment_file(file_path)
for data in commitments_data:
    graph.add_commitment(*data)


# 根据依赖关系处理承诺状态
result = graph.fulfill_commitment("1")
print(result)