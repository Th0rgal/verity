// SPDX-License-Identifier: MIT
pragma solidity ^0.8.33;

import "forge-std/Test.sol";
import "./yul/YulTestBase.sol";

contract SelfBalanceSmokeReference {
    function currentBalance() external view returns (uint256) {
        return address(this).balance;
    }

    function balancePlus(uint256 delta) external view returns (uint256) {
        return address(this).balance + delta;
    }

    receive() external payable {}
}

contract SelfBalanceSmokeTest is Test, YulTestBase {
    address internal yulContract;
    SelfBalanceSmokeReference internal referenceContract;

    function setUp() public {
        yulContract = deployCompiledVerityModule(
            "Contracts.Smoke.SelfBalanceSmoke",
            "SelfBalanceSmoke",
            _smokeYulDir()
        );
        referenceContract = new SelfBalanceSmokeReference();
    }

    function _fundBoth(uint256 amount) internal {
        vm.deal(yulContract, amount);
        vm.deal(address(referenceContract), amount);
    }

    function _assertReturnParity(bytes memory callData) internal {
        (bool yulSuccess, bytes memory yulData) = yulContract.call(callData);
        (bool refSuccess, bytes memory refData) = address(referenceContract).call(callData);

        assertEq(yulSuccess, refSuccess, "success mismatch");
        assertEq(yulData, refData, "return data mismatch");
        assertTrue(yulSuccess, "expected success");
    }

    function testCurrentBalanceMatchesSolidity() public {
        _fundBoth(1.25 ether);
        _assertReturnParity(abi.encodeWithSignature("currentBalance()"));
    }

    function testBalancePlusMatchesSolidity(uint96 balance, uint96 delta) public {
        _fundBoth(uint256(balance));
        _assertReturnParity(abi.encodeWithSignature("balancePlus(uint256)", uint256(delta)));
    }
}
