WIDTH = 253
a = 253294999597713183590858403791743516149761964605603027590918106447285982865 
a_bits = []
while a > 0:
  a_bits.insert(0, a % 2 == 1)
  a //= 2
while len(a_bits) < WIDTH:
  a_bits.insert(0, False)
print(a_bits)