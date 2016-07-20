def egcd(a, b):
  if a == 0: return (b, 0, 1)
  g, y, x = egcd(b%a, a)
  return (g, x - (b//a)*y, y)

def modinv(a, m):
  g, x, y = egcd(a, m)
  return x%m

def rsa(p, q, e):
  return modinv(e, (p-1)*(q-1))

es = (3, 5, 7, 11, 13, 17, 19)

def is_prime(p):
  if p in es: return True
  for e in es:
    if p%e == 0: return False
  return True


cases = []
for e in es:
  for p in range(3, 50, 2):
    if not is_prime(p): continue
    for q in range(3, 50, 2):
      if not is_prime(q): continue
      phi = (p-1)*(q-1)
      if phi%e == 0: continue
      if e > phi: continue
      res = rsa(p, q, e)
      cases.append((p, q, e, res))

import random

def gen_case():
  p, q, e, res = random.choice(cases)
  print('[{}, {}, {}] -> {}'.format(p, q, e, res))
  # print('[{}, {}] -> {}'.format(e, (p-1)*(q-1), res))

for i in range(10):
  gen_case()
