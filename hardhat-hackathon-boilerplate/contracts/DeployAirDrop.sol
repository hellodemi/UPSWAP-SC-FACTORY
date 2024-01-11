//// SPDX-License-Identifier: MIT
//pragma solidity ^0.8.0;
//
//import "@openzeppelin/contracts/access/Ownable.sol";
//import "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
//import "@openzeppelin/contracts/utils/math/SafeMath.sol";
//
//import "./HUPAirDrop.sol";
//import "./structs/AirDropStructs.sol";
//
//contract DeployAirDrop is Ownable {
//    using SafeMath for uint256;
//
//    address public superAccount;
//    address payable public fundAddress;
//
//    event NewAirDrop(address indexed airDrop);
//
//
//    constructor(address _superAccount, address payable _fundAddress){
//        require(_superAccount != address(0) && _superAccount != address(this), 'invalid superAccount');
//        require(_fundAddress != address(0) && _fundAddress != address(this), 'invalid superAccount');
//        superAccount = _superAccount;
//        fundAddress = _fundAddress;
//    }
//
//    function setSuperAccount(address _superAccount) public onlyOwner {
//        require(_superAccount != address(0) && _superAccount != address(this), 'invalid superAccount');
//        require(superAccount != _superAccount, 'No need to update!');
//        superAccount = _superAccount;
//    }
//
//    function setFundAddress(address payable _fundAddress) public onlyOwner {
//        require(_fundAddress != address(0) && _fundAddress != address(this), 'invalid fundAddress');
//        require(fundAddress != _fundAddress, 'No need to update!');
//        fundAddress = _fundAddress;
//    }
//
//
//    function deployAirDrop(IERC20 _airDropToken,
//        uint256 _fundPercent,
//        uint256 _amount) external payable {
//
//        require(superAccount != address(0), 'Can not create launchpad now!');
//        require(fundAddress != address(0), 'Invalid Fund Address');
//        require(msg.value >= _amount, 'Invalid amount');
//
//        HUPAirDrop airDrop = new HUPAirDrop(_airDropToken, fundAddress, _fundPercent, superAccount, _msgSender());
//
//        if (msg.value > 0) {
//            payable(fundAddress).transfer(msg.value);
//        }
//        emit NewAirDrop(address(airDrop));
//    }
//
//    function getAirDrops(address[] memory hupAirDrops) external view returns (AirDropStructs.AirDropFlashInfo[] memory) {
//
//        AirDropStructs.AirDropFlashInfo[] memory result = new AirDropStructs.AirDropFlashInfo[](hupAirDrops.length);
//        for (uint256 i = 0; i < hupAirDrops.length; i++) {
//            AirDropStructs.AirDropFlashInfo memory info;
//            HUPAirDrop hupAirDrop = HUPAirDrop(hupAirDrops[i]);
//
//            try hupAirDrop.allAllocationCount() returns (uint256  v) {
//                info.tokenAddress = address(hupAirDrop.airDropToken());
//                info.totalAllocations = v;
//                info.totalClaimedAllocations = hupAirDrop.userClaimedTokens();
//                info.totalTokens = hupAirDrop.totalAllocationTokens();
//                info.tgeDate = hupAirDrop.tgeDate();
//                info.state = hupAirDrop.airDropState();
//
//                result[i] = info;
//
//            } catch Error(string memory /*reason*/) {
//                continue;
//            } catch (bytes memory /*lowLevelData*/) {
//                continue;
//            }
//        }
//        return result;
//
//
//    }
//
//
//}
//
//
