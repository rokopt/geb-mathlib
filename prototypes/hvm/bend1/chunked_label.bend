# A "long bitstring" label: 2^k u24 chunks stored as a balanced pair tree
# with a length header, label = (k, chunks). The per-label hash XORs all
# chunks. Concatenation of two labels of equal length is one pair node,
# (k + 1, (c1, c2)); concatenation of unequal lengths would require
# rebalancing (a rotation), which is not implemented here.
# Entry: `bend run-c FILE -s OP K`, OP selecting the operation:
#   0 = hash of one label, 1 = hash of the concatenation of two labels
#   of 2^k chunks each.

def gen_chunks(k, i):
  bend k, i:
    when k != 0:
      return (fork(k - 1, 2 * i), fork(k - 1, 2 * i + 1))
    else:
      return i * 2654435 + 12345

def gen_label(k, seed):
  return (k, gen_chunks(k, seed))

def xor_chunks(k, t):
  switch k:
    case 0:
      return t
    case _:
      (a, b) = t
      return xor_chunks(k-1, a) ^ xor_chunks(k-1, b)

def hash_label(l):
  (k, t) = l
  return xor_chunks(k, t)

def concat(l1, l2):
  (k1, t1) = l1
  (k2, t2) = l2
  return (k1 + 1, (t1, t2))

def main_hash(k):
  return hash_label(gen_label(k, 0))

def main_concat(k):
  return hash_label(concat(gen_label(k, 0), gen_label(k, 1)))

def main(op, d):
  switch op:
    case 0:
      return main_hash(d)
    case _:
      return main_concat(d)
