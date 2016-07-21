def egcd(a, b):
  if a == 0: return (b, 0, 1)
  g, y, x = egcd(b%a, a)
  return (g, x - (b//a)*y, y)

def modinv(a, m):
  g, x, y = egcd(a, m)
  return x%m

def rsa(p, q, e):
  return modinv(e, (p-1)*(q-1))

es = [3, 5, 7, 11, 13, 17, 19]
def is_prime(p):
  if p in es: return True
  for e in es:
    if p%e == 0: return False
  return True


import random
def gen_rsa_cases(n):
    cases = []
    for e in es:
      for p in range(3, 50, 2):
        if not is_prime(p): continue
        for q in range(3, 50, 2):
          if not is_prime(q): continue
          phi = (p-1)*(q-1)
          if phi%e == 0: continue
          if e > phi: continue
          cases.append((p, q, e))

    for i in range(n):
        p, q, e = random.choice(cases)
        res = rsa(p, q, e)
        yield ([p, q, e], res)


# if __name__ == __main__:
#     for ([p, q, e], res) in gen_rsa_cases(10):
#         print('[{}, {}, {}] -> {}'.format(p, q, e, res))


from qset_interpreter import convert_fmt, interpret

tests = [
    [29, 47, 5],
    [37, 43, 11],
    [5, 13, 17],
    [37, 5, 11],
    [37, 37, 11],
    [7, 17, 7],
    [3, 3, 3],
    # [43, 5, 19],
    # [13, 13, 19],
    # [23, 29, 5],
    # [17, 3, 19],
]


import sys
prog = convert_fmt(sys.stdin.read())
print(prog)

# for (l, expected) in gen_rsa_cases(10):
for l in tests:
    expected = rsa(*l)
    (res, steps) = interpret(prog, l, 10000000)
    print(res == [expected], steps)
