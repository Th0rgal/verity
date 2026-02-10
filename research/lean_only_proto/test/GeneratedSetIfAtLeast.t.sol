// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedSetIfAtLeastTest is GeneratedBase {
    function testSetIfAtLeast() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selSet = 0x407cdd03;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 13, 9, 9));
        require(ok, "setIfAtLeast failed (value == min)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 13));
        require(ok, "getSlot failed (slot 13)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 9, "unexpected setIfAtLeast value");

        (ok,) = deployed.call(abi.encodeWithSelector(selSet, 14, 12, 10));
        require(ok, "setIfAtLeast failed (value > min)");

        (ok,) = deployed.call(abi.encodeWithSelector(selSet, 15, 4, 9));
        require(!ok, "setIfAtLeast should revert when value < min");
    }
}
