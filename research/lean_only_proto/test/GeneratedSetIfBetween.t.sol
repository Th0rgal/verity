// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedSetIfBetweenTest is GeneratedBase {
    function testSetIfBetween() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selSet = 0x5ebc58db;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 21, 7, 5, 10));
        require(ok, "setIfBetween failed (min < value < max)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 21));
        require(ok, "getSlot failed (slot 21)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 7, "unexpected setIfBetween value");

        (ok,) = deployed.call(abi.encodeWithSelector(selSet, 22, 5, 5, 10));
        require(!ok, "setIfBetween should revert when value <= min");

        (ok,) = deployed.call(abi.encodeWithSelector(selSet, 23, 10, 5, 10));
        require(!ok, "setIfBetween should revert when value >= max");
    }
}
