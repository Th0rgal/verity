// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "forge-std/Test.sol";
import "../src/LoanSpecHarness.sol";

contract LoanSpecHarnessTest is Test {
    LoanSpecHarness private loan;

    address private constant ALICE = address(0xA11CE);

    function setUp() public {
        loan = new LoanSpecHarness(1.25e18);
    }

    function testUpdateSpecHappy() public {
        loan.update_spec(ALICE, 200e18, 100e18);

        assertEq(loan.collateral(ALICE), 200e18);
        assertEq(loan.debt(ALICE), 100e18);
    }

    function testUpdateSpecRejectsBadHealthFactor() public {
        vm.expectRevert(Loan.HealthFactor.selector);
        loan.update_spec(ALICE, 100e18, 100e18);
    }
}
