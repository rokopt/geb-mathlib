# Full binary tree of depth d as nested native pairs (l, r); leaves are u24
# labels (the leaf's index); the shape is carried by the depth argument,
# as in HVM2's sum_tree and bitonic_sort examples.
# Entry: `bend run-c FILE -s OP D`, OP selecting the operation:
#   0 = sum, 1 = hash, 2 = eq2 (two generated trees), 3 = eqdup (one tree, duplicated).

def gen(d, i):
  bend d, i:
    when d != 0:
      return (fork(d - 1, 2 * i), fork(d - 1, 2 * i + 1))
    else:
      return i

def sum(d, t):
  switch d:
    case 0:
      return t
    case _:
      (a, b) = t
      return sum(d-1, a) + sum(d-1, b)

# u24 arithmetic wraps mod 2^24.
def hash(d, t):
  switch d:
    case 0:
      return t
    case _:
      (a, b) = t
      return hash(d-1, a) * 31 + hash(d-1, b)

def eq(d, x, y):
  switch d:
    case 0:
      return x == y
    case _:
      (a, b) = x
      (c, e) = y
      return eq(d-1, a, c) & eq(d-1, b, e)

def main_sum(d):
  return sum(d, gen(d, 0))

def main_hash(d):
  return hash(d, gen(d, 0))

def main_eq2(d):
  return eq(d, gen(d, 0), gen(d, 0))

def main_eqdup(d):
  t = gen(d, 0)
  return eq(d, t, t)

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
