# Full binary tree of depth d as an algebraic data type; leaves carry the
# u24 label i (the leaf's index in left-to-right order); nodes carry none.
# Entry: `bend run-c FILE -s OP D`, OP selecting the operation:
#   0 = sum, 1 = hash, 2 = eq2 (two generated trees),
#   3 = eqdup (one generated tree, duplicated).

type BTree:
  Node { ~left, ~right }
  Leaf { val }

def gen(d, i):
  bend d, i:
    when d != 0:
      return BTree/Node(fork(d - 1, 2 * i), fork(d - 1, 2 * i + 1))
    else:
      return BTree/Leaf(i)

def sum(t):
  fold t:
    case BTree/Node:
      return t.left + t.right
    case BTree/Leaf:
      return t.val

# u24 arithmetic wraps mod 2^24.
def hash(t):
  fold t:
    case BTree/Node:
      return t.left * 31 + t.right
    case BTree/Leaf:
      return t.val

def eq(a, b):
  match a:
    case BTree/Node:
      match b:
        case BTree/Node:
          return eq(a.left, b.left) & eq(a.right, b.right)
        case BTree/Leaf:
          return 0
    case BTree/Leaf:
      match b:
        case BTree/Node:
          return 0
        case BTree/Leaf:
          return a.val == b.val

def main_sum(d):
  return sum(gen(d, 0))

def main_hash(d):
  return hash(gen(d, 0))

def main_eq2(d):
  return eq(gen(d, 0), gen(d, 0))

def main_eqdup(d):
  t = gen(d, 0)
  return eq(t, t)

def main(op, d):
  switch op:
    case 0:
      return main_sum(d)
    case 1:
      return main_hash(d)
    case 2:
      return main_eq2(d)
    case _:
      return main_eqdup(d)
