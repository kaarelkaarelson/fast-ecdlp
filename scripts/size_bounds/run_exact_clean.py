"""Run the exact-count parts (gadgets, part1, part2) of check_network.py with the clean parameter choice."""
import time, netlib as nl
nl.choose_par = nl.choose_par_clean
import check_network as cn
t0 = time.time()
g = cn.gadget_tests(); p1, n = cn.part1(); p2 = cn.part2()
print('SUMMARY clean-par exact parts: gadgets=%s part1(instances=%d)=%s part2=%s [%.0fs]' % (g, n, p1, p2, time.time() - t0))
print('EXACT-PART PASS' if (g and p1 and p2) else 'EXACT-PART NOT PASS')
