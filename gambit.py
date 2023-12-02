import pygambit as gbt
from collections import deque

g = gbt.Game.new_tree(players=["Alice", "Bob"],
                      title="One card poker game, after Myerson (1991)")

# print("players = ",g.players)
g.append_move(g.root, g.players.chance, ["King", "Queen"])
g.insert_move(g.root, g.players.chance, 1)


print("g.root = ",g.root)
for node in g.root.children:
    print("node = ",node)

    


# str1 = g.write('native')
# print("str1 = ",str1)
# with open('./spence.efg','w') as file:
#     file.write(str1)
    
gt = gbt.Game.new_tree(players = ["Alice","Carili"],title = "test game to append children and out come")
