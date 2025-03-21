import cocotb, json, sys, random

from pathlib import Path
from cocotb.runner import get_runner, get_results
from cocotb.triggers import Timer

# directory for this homework
PROJECT_PATH = Path(__file__).resolve().parent

p = Path.cwd() / '..' / 'common' / 'python'
sys.path.append(str(p))
import cocotb_utils as cu
from cocotb_utils import assertEquals

# for deterministic random numbers
random.seed(12345)

def runCocotbTests1iter(pytestconfig):
    """run 1iter tests"""

    verilog_sources = [ PROJECT_PATH / "divider_unsigned.sv" ]
    toplevel_module = "divu_1iter"

    runr = get_runner(cu.SIM)
    runr.build(
        verilog_sources=verilog_sources,
        vhdl_sources=[],
        hdl_toplevel=toplevel_module,
        waves=True,
        includes=[PROJECT_PATH],
        build_dir=cu.SIM_BUILD_DIR,
        build_args=cu.VERILATOR_FLAGS,
    )

    runr.test(
        seed=12345,
        waves=True,
        hdl_toplevel=toplevel_module, 
        test_module="testbench_1iter", # use tests from testbench_1iter.py
        testcase=pytestconfig.option.tests, # filter tests via the `--tests` command-line flag
    )
    pass

def runCocotbTestsDivider(pytestconfig):
    """run divider tests"""

    verilog_sources = [ PROJECT_PATH / "divider_unsigned.sv" ]
    toplevel_module = "divider_unsigned"

    runr = get_runner(cu.SIM)
    runr.build(
        verilog_sources=verilog_sources,
        vhdl_sources=[],
        hdl_toplevel=toplevel_module,
        waves=True,
        includes=[PROJECT_PATH],
        build_dir=cu.SIM_BUILD_DIR,
        build_args=cu.VERILATOR_FLAGS,
    )

    runr.test(
        seed=12345,
        waves=True,
        hdl_toplevel=toplevel_module, 
        test_module=Path(__file__).stem, # use tests from the current file
        testcase=pytestconfig.option.tests, # filter tests via the `--tests` command-line flag
    )
    pass

def runCocotbTests(pytestconfig):
    """calculate scores for autograder"""
    test_results = cu.aggregateTestResults(
        get_results(Path(cu.SIM_BUILD_DIR,'runCocotbTests1iter.None')),
        get_results(Path(cu.SIM_BUILD_DIR,'runCocotbTestsDivider.None')),
    )
    # 1 point per cocotb test
    points = { 'pointsEarned': test_results['tests_passed'], 'pointsPossible': test_results['tests_total'] }
    with open(cu.POINTS_FILE, 'w') as f:
        json.dump(points, f, indent=2)
        pass
    pass


#########################
## TEST CASES ARE HERE ##
#########################

@cocotb.test()
async def test_simple0(dut):
    await Timer(1, "ns")
    dut.i_dividend.value = 4
    dut.i_divisor.value = 2
    await Timer(1, "ns")
    assertEquals(2, dut.o_quotient.value)
    assertEquals(0, dut.o_remainder.value)

@cocotb.test()
async def test_simple1(dut):
    await Timer(1, "ns")
    dut.i_dividend.value = 4
    dut.i_divisor.value = 4
    await Timer(1, "ns")
    assertEquals(1, dut.o_quotient.value)
    assertEquals(0, dut.o_remainder.value)

@cocotb.test()
async def test_simple2(dut):
    await Timer(1, "ns")
    dut.i_dividend.value = 10
    dut.i_divisor.value = 4
    await Timer(1, "ns")
    assertEquals(2, dut.o_quotient.value)
    assertEquals(2, dut.o_remainder.value)

@cocotb.test()
async def test_simple3(dut):
    await Timer(1, "ns")
    dut.i_dividend.value = 2
    dut.i_divisor.value = 4
    await Timer(1, "ns")
    assertEquals(0, dut.o_quotient.value)
    assertEquals(2, dut.o_remainder.value)

@cocotb.test()
async def test_random1k(dut):
    for i in range(1000):
        await Timer(1, "ns")
        dividend = random.randrange(0,2**32)
        divisor = random.randrange(1,2**32) # NB: no divide-by-zero
        dut.i_dividend.value = dividend
        dut.i_divisor.value = divisor
        await Timer(1, "ns")

        exp_quotient = int(dividend / divisor)
        exp_remainder = dividend % divisor

        msg = f'expected {dividend} / {divisor} = {exp_quotient} rem {exp_remainder}\n'
        msg += f'but was quot={dut.o_quotient.value} rem={dut.o_remainder.value}'
        assertEquals(exp_quotient, dut.o_quotient.value, msg)
        assertEquals(exp_remainder, dut.o_remainder.value, msg)
        pass
    pass

@cocotb.test()
async def test_divisor1(dut):
    """
    Test dividing by 1 for random dividends.
    Quotient should equal the dividend, remainder should be 0.
    """
    for _ in range(10):
        await Timer(1, "ns")
        dividend = random.randrange(0, 2**32)
        divisor = 1
        dut.i_dividend.value = dividend
        dut.i_divisor.value = divisor
        await Timer(1, "ns")

        exp_quotient = dividend
        exp_remainder = 0

        msg = f"Dividing {dividend} by 1 should be quotient={exp_quotient}, remainder={exp_remainder}"
        cu.assertEquals(exp_quotient, dut.o_quotient.value, msg)
        cu.assertEquals(exp_remainder, dut.o_remainder.value, msg)
    pass


@cocotb.test()
async def test_dividend0(dut):
    """
    Test a zero dividend with random divisors.
    Quotient should be 0, remainder should be 0.
    """
    for _ in range(10):
        await Timer(1, "ns")
        dividend = 0
        divisor = random.randrange(1, 2**32)  # nonzero
        dut.i_dividend.value = dividend
        dut.i_divisor.value = divisor
        await Timer(1, "ns")

        exp_quotient = 0
        exp_remainder = 0

        msg = f"Dividing 0 by {divisor} should be quotient=0, remainder=0"
        cu.assertEquals(exp_quotient, dut.o_quotient.value, msg)
        cu.assertEquals(exp_remainder, dut.o_remainder.value, msg)
    pass


@cocotb.test()
async def test_divisor_larger_than_dividend(dut):
    """
    If the divisor is larger than the dividend,
    then quotient should be 0, remainder should be the dividend.
    """
    for _ in range(10):
        await Timer(1, "ns")
        dividend = random.randrange(0, 2**16)
        # Make divisor definitely larger by adding something well above 2^16
        divisor = random.randrange(2**20, 2**32)

        dut.i_dividend.value = dividend
        dut.i_divisor.value = divisor
        await Timer(1, "ns")

        exp_quotient = 0
        exp_remainder = dividend

        msg = f"{dividend} / {divisor} => expected quotient=0, remainder={dividend}"
        cu.assertEquals(exp_quotient, dut.o_quotient.value, msg)
        cu.assertEquals(exp_remainder, dut.o_remainder.value, msg)
    pass


@cocotb.test()
async def test_near_max_values(dut):
    """
    Test near maximum 32-bit values for both dividend and divisor.
    """
    test_values = [
        (2**31 - 1, 2**31 - 1),
        (2**31, 2**31 - 1),
        (2**31 - 1, 2**31),
        (0xFFFFFFFF, 0xFFFFFFFE),
        (0xFFFFFFFE, 0xFFFFFFFF),
    ]
    for dividend, divisor in test_values:
        await Timer(1, "ns")
        dut.i_dividend.value = dividend
        dut.i_divisor.value = divisor
        await Timer(1, "ns")

        exp_quotient = int(dividend // divisor)  # Python's floor division
        exp_remainder = dividend % divisor

        msg = f"Dividing {dividend} by {divisor}"
        cu.assertEquals(exp_quotient, dut.o_quotient.value, msg + f" => quotient mismatch")
        cu.assertEquals(exp_remainder, dut.o_remainder.value, msg + f" => remainder mismatch")
    pass


@cocotb.test()
async def test_zero_dividend(dut):
    """
    0 / X -> quotient=0, remainder=0
    """
    await Timer(1, "ns")
    dut.i_dividend.value = 0
    # picking some random nonzero divisor
    dut.i_divisor.value = 1234
    await Timer(1, "ns")

    cu.assertEquals(0, dut.o_quotient.value, "0 / 1234 should have quotient=0")
    cu.assertEquals(0, dut.o_remainder.value, "0 / 1234 should have remainder=0")


@cocotb.test()
async def test_divisor_larger(dut):
    """
    If the divisor > dividend, quotient=0, remainder=dividend
    """
    await Timer(1, "ns")
    dut.i_dividend.value = 10
    dut.i_divisor.value = 9999
    await Timer(1, "ns")

    cu.assertEquals(0, dut.o_quotient.value, "10 / 9999 should have quotient=0")
    cu.assertEquals(10, dut.o_remainder.value, "10 / 9999 should have remainder=10")


@cocotb.test()
async def test_divisor1(dut):
    """
    X / 1 => quotient=X, remainder=0
    """
    test_vals = [0, 1, 2, 9999, 2 ** 31, 2 ** 32 - 1]
    for val in test_vals:
        await Timer(1, "ns")
        dut.i_dividend.value = val
        dut.i_divisor.value = 1
        await Timer(1, "ns")

        msg = f"Dividing {val} by 1"
        cu.assertEquals(val, dut.o_quotient.value, msg + " => quotient should be same as dividend")
        cu.assertEquals(0, dut.o_remainder.value, msg + " => remainder should be 0")


@cocotb.test()
async def test_large_values(dut):
    """
    Tests near-maximum 32-bit values
    """
    # Some interesting corner cases near the 32-bit boundary
    test_cases = [
        (0xFFFFFFFE, 0xFFFFFFFF),  # divisor > dividend
        (0xFFFFFFFF, 0xFFFFFFFE),  # remainder=1
        (0xFFFFFFFF, 1),  # large / small
        (2 ** 31, 2 ** 31 - 1),  # 2^31 / (2^31 - 1)
    ]
    for (dividend, divisor) in test_cases:
        await Timer(1, "ns")
        dut.i_dividend.value = dividend
        dut.i_divisor.value = divisor
        await Timer(1, "ns")

        exp_quot = dividend // divisor
        exp_rem = dividend % divisor

        msg = f"Dividing {dividend} by {divisor}"
        cu.assertEquals(exp_quot, dut.o_quotient.value, msg + " => quotient mismatch")
        cu.assertEquals(exp_rem, dut.o_remainder.value, msg + " => remainder mismatch")
