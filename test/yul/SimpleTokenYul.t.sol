// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

import "./YulTestBase.sol";
import "../../examples/solidity/SimpleToken.sol";

interface ISimpleToken {
    function mint(address to, uint256 amount) external;
    function transfer(address to, uint256 amount) external;
    function balanceOf(address addr) external view returns (uint256);
    function totalSupply() external view returns (uint256);
    function owner() external view returns (address);
}

contract SimpleTokenYulTest is YulTestBase {
    ISimpleToken private yul;
    SimpleToken private solidityImpl;
    address private alice = address(0xA11CE);
    address private bob = address(0xB0B);

    function setUp() public {
        yul = ISimpleToken(deployYulWithArgs("SimpleToken", abi.encode(alice)));
        solidityImpl = new SimpleToken(alice);
    }

    function testOwnerAndSupply() public {
        assertEq(solidityImpl.owner(), yul.owner());
        assertEq(solidityImpl.totalSupply(), yul.totalSupply());
    }

    function testMintAndTransfer() public {
        vm.prank(alice);
        solidityImpl.mint(alice, 1000);
        vm.prank(alice);
        yul.mint(alice, 1000);

        vm.prank(alice);
        solidityImpl.transfer(bob, 300);
        vm.prank(alice);
        yul.transfer(bob, 300);

        assertEq(solidityImpl.balanceOf(alice), yul.balanceOf(alice));
        assertEq(solidityImpl.balanceOf(bob), yul.balanceOf(bob));
        assertEq(solidityImpl.totalSupply(), yul.totalSupply());
    }
}
