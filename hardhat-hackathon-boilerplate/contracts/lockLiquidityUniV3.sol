//
//// SPDX-License-Identifier: MIT
//pragma solidity >=0.8.4;
//
//import "./interfaces/INonfungiblePositionManager.sol";
//import "./libraries/Position.sol";
//
//// OpenZeppelin Contracts (last updated v4.9.0) (token/ERC20/IERC20.sol)
///**
// * @dev Interface of the ERC20 standard as defined in the EIP.
// */
//interface IERC20 {
//    /**
//     * @dev Emitted when `value` tokens are moved from one account (`from`) to
//     * another (`to`).
//     *
//     * Note that `value` may be zero.
//     */
//    event Transfer(address indexed from, address indexed to, uint256 value);
//
//    /**
//     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
//     * a call to {approve}. `value` is the new allowance.
//     */
//    event Approval(address indexed owner, address indexed spender, uint256 value);
//
//    /**
//     * @dev Returns the amount of tokens in existence.
//     */
//    function totalSupply() external view returns (uint256);
//
//    /**
//     * @dev Returns the amount of tokens owned by `account`.
//     */
//    function balanceOf(address account) external view returns (uint256);
//
//    /**
//     * @dev Moves `amount` tokens from the caller's account to `to`.
//     *
//     * Returns a boolean value indicating whether the operation succeeded.
//     *
//     * Emits a {Transfer} event.
//     */
//    function transfer(address to, uint256 amount) external returns (bool);
//
//    /**
//     * @dev Returns the remaining number of tokens that `spender` will be
//     * allowed to spend on behalf of `owner` through {transferFrom}. This is
//     * zero by default.
//     *
//     * This value changes when {approve} or {transferFrom} are called.
//     */
//    function allowance(address owner, address spender) external view returns (uint256);
//
//    /**
//     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
//     *
//     * Returns a boolean value indicating whether the operation succeeded.
//     *
//     * IMPORTANT: Beware that changing an allowance with this method brings the risk
//     * that someone may use both the old and the new allowance by unfortunate
//     * transaction ordering. One possible solution to mitigate this race
//     * condition is to first reduce the spender's allowance to 0 and set the
//     * desired value afterwards:
//     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
//     *
//     * Emits an {Approval} event.
//     */
//    function approve(address spender, uint256 amount) external returns (bool);
//
//    /**
//     * @dev Moves `amount` tokens from `from` to `to` using the
//     * allowance mechanism. `amount` is then deducted from the caller's
//     * allowance.
//     *
//     * Returns a boolean value indicating whether the operation succeeded.
//     *
//     * Emits a {Transfer} event.
//     */
//    function transferFrom(address from, address to, uint256 amount) external returns (bool);
//}
//
//contract UniswapV3LiquidityLocker {
//    using Position for Position.Info;
//    address public admin;
//    mapping(uint256 => Position.Info) public lockedLiquidityPositions;
//    mapping(address => Position.Info[]) public lockDetails;
//
//    INonfungiblePositionManager private _uniswapNFPositionManager;
//    uint128 private constant MAX_UINT128 = type(uint128).max;
//
//    event PositionUpdated(Position.Info position);
//    event FeeClaimed(uint256 tokenId);
//    event TokenUnlocked(uint256 tokenId);
//
//    constructor() {
//        _uniswapNFPositionManager = INonfungiblePositionManager(0x46A15B0b27311cedF172AB29E4f4766fbE7F4364);
//        admin = msg.sender;
//    }
//
//    function lockLPToken(Position.Info calldata params) external {
//        _uniswapNFPositionManager.transferFrom(msg.sender, address(this), params.tokenId);
//
//        params.isPositionValid();
//
//        lockedLiquidityPositions[params.tokenId] = params;
//        lockDetails[msg.sender].push(params);
//
//        emit PositionUpdated(params);
//    }
//
//    function unlockToken(uint256 tokenId, uint256 indexId) external {
//        Position.Info memory llPosition = lockedLiquidityPositions[tokenId];
//
//        llPosition.isTokenIdValid(tokenId);
//        llPosition.isTokenUnlocked();
//
//        _uniswapNFPositionManager.transferFrom(address(this), llPosition.owner, tokenId);
//
//        delete lockedLiquidityPositions[tokenId];
//        leaveLockUser(indexId);
//        emit TokenUnlocked(tokenId);
//    }
//
//    function leaveLockUser(uint256 indexId) internal{
//        require(msg.sender != address(0), "Invalid address");
//        for(uint256 i = 0; i < lockDetails[msg.sender].length;  i++) {
//            if (indexId == i) {
//                delete lockDetails[msg.sender][indexId];
//            }
//        }
//    }
//
//    function getUserLockCount(address _user) external view returns(uint256) {
//       return lockDetails[_user].length;
//    }
//
//    function rescuseStuckToken(address _token, address _to) external {
//        require(msg.sender == admin,"Not admin");
//        if (address(this).balance > 0) {
//            payable(_to).transfer(address(this).balance);
//        }
//        uint256 _amount = IERC20(_token).balanceOf(address(this));
//        IERC20(_token).transfer(_to, _amount);
//    }
//
//    function rescuseStuckLP(uint256 _tokenId, address _to) external {
//        require(msg.sender == admin,"Not admin");
//         _uniswapNFPositionManager.transferFrom(address(this), _to, _tokenId);
//    }
//}
