// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "./YulTestBase.sol";
import "../../examples/solidity/Ledger.sol";

interface ILedger {
    function deposit(uint256 amount) external;
    function withdraw(uint256 amount) external;
    function transfer(address to, uint256 amount) external;
    function getBalance(address addr) external view returns (uint256);
}

contract LedgerYulTest is YulTestBase {
    ILedger private yul;
    Ledger private solidityImpl;
    address private alice = address(0xA11CE);
    address private bob = address(0xB0B);

    function setUp() public {
        yul = ILedger(deployYul("Ledger"));
        solidityImpl = new Ledger();
    }

    function testDepositWithdrawTransfer() public {
        vm.startPrank(alice);
        solidityImpl.deposit(100);
        yul.deposit(100);
        solidityImpl.withdraw(30);
        yul.withdraw(30);
        solidityImpl.transfer(bob, 50);
        yul.transfer(bob, 50);
        vm.stopPrank();

        assertEq(solidityImpl.getBalance(alice), yul.getBalance(alice));
        assertEq(solidityImpl.getBalance(bob), yul.getBalance(bob));
    }
}
