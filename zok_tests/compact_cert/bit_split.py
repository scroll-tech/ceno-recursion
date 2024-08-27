WIDTH = 253
a = 4415915127126372096757067153593537022657929051278082364476489088715040314973
a_bits = []
while a > 0:
  a_bits.insert(0, a % 2 == 1)
  a //= 2
while len(a_bits) < WIDTH:
  a_bits.insert(0, False)
print(a_bits)