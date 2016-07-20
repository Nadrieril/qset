class QSet:
    def __init__(self, input=None):
        self.__repr__=self.__str__
        self.qset = {}
        if input!=None:
            for item in input:
                self.add_item(item)
    def add_item(self, item, amt=1):
        if item in self.qset:
            self.qset[item]+=amt
            # if self.qset[item]==0:
            #     del self.qset[item]
        else:
            self.qset[item]=amt
    def add_qset(self, aqset):
        for item in aqset.qset:
            self.add_item(item, aqset.qset[item])
    def remove_qset(self, aqset):
        for item in aqset.qset:
            self.add_item(item, -aqset.qset[item])
    def contains_qset(self, aqset):
        for item in aqset.qset:
            if item in self.qset:
                if self.qset[item]<aqset.qset[item]:
                    return False
            else:
                return False
        return True
    def is_empty(self):
        return len(self.qset)==0
    def __str__(self):
        return str(self.qset)

def parse(x):
    steps = x.strip()
    steps = steps.split(',')
    reps = []
    for step in steps:
        rep = [y.strip() for y in step.split('/')]
        if len(rep)!=2:
            raise Exception("Failed to parse input!")
        reps.append(rep)
    return [[QSet([] if x.split(' ')==[''] else x.split(' ')) for x in vals] for vals in reps]

def interpret_step(program, qset):
    for process in program:
        if qset.contains_qset(process[1]):
            qset.remove_qset(process[1])
            qset.add_qset(process[0])
            return False
    return True

def print_qset(qset):
    keys = sorted([k for k in qset.keys() if k[0]!="l" ])
    labels = [k for k in qset.keys() if k[0]=="l" and qset[k]>0 ]
    print(",  ".join("%3s: %2d" % (k, qset[k]) for k in labels+keys))

def interpret(program, input, maxsteps=100):
    try:
        program = parse(program)
        qset = QSet()
        for x in range(len(input)):
            if type(input[x]) is int:
                qset.add_item('i%i'%x, input[x])
            else:
                raise Exception("Invalid input type")
        step = 0
        while True:
            if step==maxsteps:
                raise Exception("Too many execution steps!")
            # print_qset(qset.qset)
            ret = interpret_step(program, qset)
            if ret:
                break
            step += 1
        success = True
        outputs = {}
        for key in qset.qset:
            if len(key)>1:
                if key[0]=="o":
                    idx = key[1:]
                    idx = int(idx)
                    outputs[idx] = qset.qset[key]
            else:
                success = False
        if success:
            outputs_arr = []
            for x in range(len(outputs)):
                if x in outputs:
                    outputs_arr.append(outputs[x])
                else:
                    raise Exception("Invalid output!")
            return outputs_arr, step
        else:
            raise Exception("Invalid output!")
    except Exception as e:
        return ",".join(e.args)


multiplication = """
f0: i0 i1 > o0 x0 i1
f0 i1 > f1
f1: x0 > i0
f1 > f0
i1 > i1 f0
i0 >
f0 >
"""


def convert(o):
    o = o.split(':')
    if len(o) > 1:
        flags = o[0]
        o = o[1]
    else:
        flags = None
        o = o[0]
    o = [x.strip() for x in o.split(">")]

    if flags:
        o[0] += " "+flags
        o[1] += " "+flags
    return "/".join(o[::-1])

import sys
prog = sys.stdin.read()
prog = ",".join([convert(x) for x in prog.strip().split('\n') if x[0] != '#'])
print(prog)

print(interpret(prog, list(map(int, sys.argv[1:])), 10000000))

# def sqrt(x):
#     s = 0
#     t = 1
#     z = 1
#     x += 1
#     while x > 0:
#         x -= 1
#         if z == 0:
#             t += 2
#             z += t
#             s += 1
#         z -= 1
#     return s
#
# for i in range(10+1):
#     print(sqrt(i*i))

# def ecldiv(a, b):
#     return (a // b, a % b)
#
# def sub(a, b):
#     return (a - min(a, b), b - min(a, b))
#
# def bezout(a, b):
#     r0=a
#     r1=b
#     s0=1
#     s1=0
#     t0=0
#     t1=1
#     while r1 != 0:
#         tmp0 = r1
#         (q, r) = ecldiv(r0, r1)
#         r0 = tmp0
#         r1 = r
#         q_ = q
#
#         tmp1 = s1
#         tmp0 = s1*q
#         (s0, tmp0) = sub(s0, tmp0)
#         nincr = 0
#         while tmp0 > 0:
#             s0 = b
#             (tmp0, s0) = sub(tmp0, s0)
#             # nincr += 1
#
#         s1 = s0
#         s0 = tmp1
#
#         # (t0, t1) = (t1, t0 - nincr*a - q*t1)
#     return s0
#
# print(bezout(5, 12)) # -> 5
# print()
# print(bezout(5, 156816)) # -> 125453
# print()
# print(bezout(11, 32)) # -> 3
# print()
# print(bezout(13, 40)) # -> 37
# print()
