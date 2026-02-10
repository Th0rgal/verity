// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

import "./GeneratedBase.t.sol";

contract GeneratedSetIfNonZeroAndLessTest is GeneratedBase {
    function testSetIfNonZeroAndLess() public {
        bytes memory creation = _readHexFile("out/example.creation.bin");
        address deployed = _deploy(creation);

        bytes4 selSet = 0x8ba43d8f;
        bytes4 selGet = 0x7eba7ba6;

        (bool ok,) = deployed.call(abi.encodeWithSelector(selSet, 21, 7, 10));
        require(ok, "setIfNonZeroAndLess failed (nonzero and below max)");

        bytes memory data;
        (ok, data) = deployed.call(abi.encodeWithSelector(selGet, 21));
        require(ok, "getSlot failed (slot 21)");
        uint256 val = abi.decode(data, (uint256));
        require(val == 7, "unexpected setIfNonZeroAndLess value");

        (ok,) = deployed.call(abi.encodeWithSelector(selSet, 22, 0, 10));
        require(!ok, "setIfNonZeroAndLess should revert when value == 0");

        (ok,) = deployed.call(abi.encodeWithSelector(selSet, 23, 10, 10));
        require(!ok, "setIfNonZeroAndLess should revert when value >= max");
    }
}
