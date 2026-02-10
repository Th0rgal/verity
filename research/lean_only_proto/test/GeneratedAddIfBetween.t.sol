// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedAddIfBetweenTest is GeneratedBase {
    function testAddIfBetween() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selAdd = 0xbc0fcb79;
        bytes4 selSet = 0xf2c298be;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 8, 10));
        require(ok, "setSlot failed (slot 8)");

        (ok,) = deployed.call(abi.encodeWithSelector(selAdd, 8, 5, 3, 9));
        require(ok, "addIfBetween failed (min < delta < max)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 8));
        require(ok, "getSlot failed (slot 8)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 15, "unexpected addIfBetween value");

        (ok,) = deployed.call(abi.encodeWithSelector(selAdd, 9, 3, 3, 9));
        require(!ok, "addIfBetween should revert when delta <= min");

        (ok,) = deployed.call(abi.encodeWithSelector(selAdd, 10, 9, 3, 9));
        require(!ok, "addIfBetween should revert when delta >= max");
    }
}
