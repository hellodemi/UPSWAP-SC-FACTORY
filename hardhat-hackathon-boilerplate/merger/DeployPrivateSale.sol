pragma solidity ^0.8.0;


// 
/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }
}

// 
/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor() {
        _setOwner(_msgSender());
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(owner() == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _setOwner(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        _setOwner(newOwner);
    }

    function _setOwner(address newOwner) private {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

// 
/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

// 
/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        assembly {
            size := extcodesize(account)
        }
        return size > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) private pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

// 
/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
        }
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) {
            // Return data is optional
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}

// 
/**
 * @dev Library for managing
 * https://en.wikipedia.org/wiki/Set_(abstract_data_type)[sets] of primitive
 * types.
 *
 * Sets have the following properties:
 *
 * - Elements are added, removed, and checked for existence in constant time
 * (O(1)).
 * - Elements are enumerated in O(n). No guarantees are made on the ordering.
 *
 * ```
 * contract Example {
 *     // Add the library methods
 *     using EnumerableSet for EnumerableSet.AddressSet;
 *
 *     // Declare a set state variable
 *     EnumerableSet.AddressSet private mySet;
 * }
 * ```
 *
 * As of v3.3.0, sets of type `bytes32` (`Bytes32Set`), `address` (`AddressSet`)
 * and `uint256` (`UintSet`) are supported.
 */
library EnumerableSet {
    // To implement this library for multiple types with as little code
    // repetition as possible, we write it in terms of a generic Set type with
    // bytes32 values.
    // The Set implementation uses private functions, and user-facing
    // implementations (such as AddressSet) are just wrappers around the
    // underlying Set.
    // This means that we can only create new EnumerableSets for types that fit
    // in bytes32.

    struct Set {
        // Storage of set values
        bytes32[] _values;
        // Position of the value in the `values` array, plus 1 because index 0
        // means a value is not in the set.
        mapping(bytes32 => uint256) _indexes;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function _add(Set storage set, bytes32 value) private returns (bool) {
        if (!_contains(set, value)) {
            set._values.push(value);
            // The value is stored at length-1, but we add 1 to all indexes
            // and use 0 as a sentinel value
            set._indexes[value] = set._values.length;
            return true;
        } else {
            return false;
        }
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function _remove(Set storage set, bytes32 value) private returns (bool) {
        // We read and store the value's index to prevent multiple reads from the same storage slot
        uint256 valueIndex = set._indexes[value];

        if (valueIndex != 0) {
            // Equivalent to contains(set, value)
            // To delete an element from the _values array in O(1), we swap the element to delete with the last one in
            // the array, and then remove the last element (sometimes called as 'swap and pop').
            // This modifies the order of the array, as noted in {at}.

            uint256 toDeleteIndex = valueIndex - 1;
            uint256 lastIndex = set._values.length - 1;

            if (lastIndex != toDeleteIndex) {
                bytes32 lastvalue = set._values[lastIndex];

                // Move the last value to the index where the value to delete is
                set._values[toDeleteIndex] = lastvalue;
                // Update the index for the moved value
                set._indexes[lastvalue] = valueIndex; // Replace lastvalue's index to valueIndex
            }

            // Delete the slot where the moved value was stored
            set._values.pop();

            // Delete the index for the deleted slot
            delete set._indexes[value];

            return true;
        } else {
            return false;
        }
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function _contains(Set storage set, bytes32 value) private view returns (bool) {
        return set._indexes[value] != 0;
    }

    /**
     * @dev Returns the number of values on the set. O(1).
     */
    function _length(Set storage set) private view returns (uint256) {
        return set._values.length;
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function _at(Set storage set, uint256 index) private view returns (bytes32) {
        return set._values[index];
    }

    // Bytes32Set

    struct Bytes32Set {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _add(set._inner, value);
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(Bytes32Set storage set, bytes32 value) internal returns (bool) {
        return _remove(set._inner, value);
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(Bytes32Set storage set, bytes32 value) internal view returns (bool) {
        return _contains(set._inner, value);
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(Bytes32Set storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function at(Bytes32Set storage set, uint256 index) internal view returns (bytes32) {
        return _at(set._inner, index);
    }

    // AddressSet

    struct AddressSet {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(AddressSet storage set, address value) internal returns (bool) {
        return _add(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(AddressSet storage set, address value) internal returns (bool) {
        return _remove(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(AddressSet storage set, address value) internal view returns (bool) {
        return _contains(set._inner, bytes32(uint256(uint160(value))));
    }

    /**
     * @dev Returns the number of values in the set. O(1).
     */
    function length(AddressSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function at(AddressSet storage set, uint256 index) internal view returns (address) {
        return address(uint160(uint256(_at(set._inner, index))));
    }

    // UintSet

    struct UintSet {
        Set _inner;
    }

    /**
     * @dev Add a value to a set. O(1).
     *
     * Returns true if the value was added to the set, that is if it was not
     * already present.
     */
    function add(UintSet storage set, uint256 value) internal returns (bool) {
        return _add(set._inner, bytes32(value));
    }

    /**
     * @dev Removes a value from a set. O(1).
     *
     * Returns true if the value was removed from the set, that is if it was
     * present.
     */
    function remove(UintSet storage set, uint256 value) internal returns (bool) {
        return _remove(set._inner, bytes32(value));
    }

    /**
     * @dev Returns true if the value is in the set. O(1).
     */
    function contains(UintSet storage set, uint256 value) internal view returns (bool) {
        return _contains(set._inner, bytes32(value));
    }

    /**
     * @dev Returns the number of values on the set. O(1).
     */
    function length(UintSet storage set) internal view returns (uint256) {
        return _length(set._inner);
    }

    /**
     * @dev Returns the value stored at position `index` in the set. O(1).
     *
     * Note that there are no guarantees on the ordering of values inside the
     * array, and it may change when more values are added or removed.
     *
     * Requirements:
     *
     * - `index` must be strictly less than {length}.
     */
    function at(UintSet storage set, uint256 index) internal view returns (uint256) {
        return uint256(_at(set._inner, index));
    }
}

// 
/**
 * @dev Contract module which allows children to implement an emergency stop
 * mechanism that can be triggered by an authorized account.
 *
 * This module is used through inheritance. It will make available the
 * modifiers `whenNotPaused` and `whenPaused`, which can be applied to
 * the functions of your contract. Note that they will not be pausable by
 * simply including this module, only once the modifiers are put in place.
 */
abstract contract Pausable is Context {
    /**
     * @dev Emitted when the pause is triggered by `account`.
     */
    event Paused(address account);

    /**
     * @dev Emitted when the pause is lifted by `account`.
     */
    event Unpaused(address account);

    bool private _paused;

    /**
     * @dev Initializes the contract in unpaused state.
     */
    constructor() {
        _paused = false;
    }

    /**
     * @dev Returns true if the contract is paused, and false otherwise.
     */
    function paused() public view virtual returns (bool) {
        return _paused;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is not paused.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    modifier whenNotPaused() {
        require(!paused(), "Pausable: paused");
        _;
    }

    /**
     * @dev Modifier to make a function callable only when the contract is paused.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    modifier whenPaused() {
        require(paused(), "Pausable: not paused");
        _;
    }

    /**
     * @dev Triggers stopped state.
     *
     * Requirements:
     *
     * - The contract must not be paused.
     */
    function _pause() internal virtual whenNotPaused {
        _paused = true;
        emit Paused(_msgSender());
    }

    /**
     * @dev Returns to normal state.
     *
     * Requirements:
     *
     * - The contract must be paused.
     */
    function _unpause() internal virtual whenPaused {
        _paused = false;
        emit Unpaused(_msgSender());
    }
}

// 
// CAUTION
// This version of SafeMath should only be used with Solidity 0.8 or later,
// because it relies on the compiler's built in overflow checks.
/**
 * @dev Wrappers over Solidity's arithmetic operations.
 *
 * NOTE: `SafeMath` is no longer needed starting with Solidity 0.8. The compiler
 * now has built in overflow checking.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            uint256 c = a + b;
            if (c < a) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the substraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b > a) return (false, 0);
            return (true, a - b);
        }
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
            // benefit is lost if 'b' is also tested.
            // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
            if (a == 0) return (true, 0);
            uint256 c = a * b;
            if (c / a != b) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a / b);
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a % b);
        }
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator.
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b <= a, errorMessage);
            return a - b;
        }
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a / b;
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a % b;
        }
    }
}

// 
/// @title Contains 512-bit math functions
/// @notice Facilitates multiplication and division that can have overflow of an intermediate value without any loss of precision
/// @dev Handles "phantom overflow" i.e., allows multiplication and division where an intermediate value overflows 256 bits
library FullMath {
  /// @notice Calculates floor(a×b÷denominator) with full precision. Throws if result overflows a uint256 or denominator == 0
  /// @param a The multiplicand
  /// @param b The multiplier
  /// @param denominator The divisor
  /// @return result The 256-bit result
  /// @dev Credit to Remco Bloemen under MIT license https://xn--2-umb.com/21/muldiv
  function mulDiv(
    uint256 a,
    uint256 b,
    uint256 denominator
  ) internal pure returns (uint256 result) {
    // 512-bit multiply [prod1 prod0] = a * b
    // Compute the product mod 2**256 and mod 2**256 - 1
    // then use the Chinese Remainder Theorem to reconstruct
    // the 512 bit result. The result is stored in two 256
    // variables such that product = prod1 * 2**256 + prod0
    uint256 prod0; // Least significant 256 bits of the product
    uint256 prod1; // Most significant 256 bits of the product
    assembly {
      let mm := mulmod(a, b, not(0))
      prod0 := mul(a, b)
      prod1 := sub(sub(mm, prod0), lt(mm, prod0))
    }

    // Handle non-overflow cases, 256 by 256 division
    if (prod1 == 0) {
      require(denominator > 0);
      assembly {
        result := div(prod0, denominator)
      }
      return result;
    }

    // Make sure the result is less than 2**256.
    // Also prevents denominator == 0
    require(denominator > prod1);

    ///////////////////////////////////////////////
    // 512 by 256 division.
    ///////////////////////////////////////////////

    // Make division exact by subtracting the remainder from [prod1 prod0]
    // Compute remainder using mulmod
    uint256 remainder;
    assembly {
      remainder := mulmod(a, b, denominator)
    }
    // Subtract 256 bit number from 512 bit number
    assembly {
      prod1 := sub(prod1, gt(remainder, prod0))
      prod0 := sub(prod0, remainder)
    }

    // Factor powers of two out of denominator
    // Compute largest power of two divisor of denominator.
    // Always >= 1.
    unchecked {
      uint256 twos = (type(uint256).max - denominator + 1) & denominator;
      // Divide denominator by power of two
      assembly {
        denominator := div(denominator, twos)
      }

      // Divide [prod1 prod0] by the factors of two
      assembly {
        prod0 := div(prod0, twos)
      }
      // Shift in bits from prod1 into prod0. For this we need
      // to flip `twos` such that it is 2**256 / twos.
      // If twos is zero, then it becomes one
      assembly {
        twos := add(div(sub(0, twos), twos), 1)
      }
      prod0 |= prod1 * twos;

      // Invert denominator mod 2**256
      // Now that denominator is an odd number, it has an inverse
      // modulo 2**256 such that denominator * inv = 1 mod 2**256.
      // Compute the inverse by starting with a seed that is correct
      // correct for four bits. That is, denominator * inv = 1 mod 2**4
      uint256 inv = (3 * denominator) ^ 2;
      // Now use Newton-Raphson iteration to improve the precision.
      // Thanks to Hensel's lifting lemma, this also works in modular
      // arithmetic, doubling the correct bits in each step.
      inv *= 2 - denominator * inv; // inverse mod 2**8
      inv *= 2 - denominator * inv; // inverse mod 2**16
      inv *= 2 - denominator * inv; // inverse mod 2**32
      inv *= 2 - denominator * inv; // inverse mod 2**64
      inv *= 2 - denominator * inv; // inverse mod 2**128
      inv *= 2 - denominator * inv; // inverse mod 2**256

      // Because the division is now exact we can divide by multiplying
      // with the modular inverse of denominator. This will give us the
      // correct result modulo 2**256. Since the precoditions guarantee
      // that the outcome is less than 2**256, this is the final result.
      // We don't need to compute the high bits of the result and prod1
      // is no longer required.
      result = prod0 * inv;
      return result;
    }
  }
}

// 
library PrivateSaleStructs {

    struct DeployInfo {
        address payable fundAddress;
        uint256 fundPercent;
        address superAccount;
        address deployer;
        address signer;
        uint256 penaltyFeePercent;
    }

    struct PrivateSaleInfo {
        address currency;
        bool isWhitelist;
        uint256 softCap;
        uint256 hardCap;
        uint256 minInvest;
        uint256 maxInvest;
        uint256 startTime;
        uint256 endTime;
    }

    struct VestingInfo {
        uint256 tgeBps;
        uint256 cycle;
        uint256 cycleBps;
    }

}

// 
contract PrivateSale is Ownable, Pausable {
    using EnumerableSet for EnumerableSet.AddressSet;
    using SafeMath for uint256;
    using SafeERC20 for IERC20;



    struct InvestInfo {
        address user;
        uint256 totalInvestment;
        bool refund;
    }


    mapping(address => bool) public adminAccounts;
    mapping(address => bool) public superAccounts;
    uint256 public privateSaleState; // 1 running||available, 2 finalize, 3 cancel



    modifier onlyWhitelistAdmin() {
        require(adminAccounts[msg.sender], "Only Admin");
        _;
    }

    modifier onlySuperAccount() {
        require(superAccounts[msg.sender], "Only Super");
        _;
    }

    function whiteListAdmins(address _user, bool _whiteList) public onlySuperAccount {
        adminAccounts[_user] = _whiteList;
    }

    modifier onlyRunning() {
        require(privateSaleState == 1, "Not available pool");
        _;
    }

    EnumerableSet.AddressSet private _investedUsers;

    mapping(address => InvestInfo) public investInfos; // user => amounts


    address payable public fundAddress;
    uint256 public fundPercent = 500;

    uint256 public constant ZOOM = 10_000;
    uint256 public penaltyFeePercent = 1000;
    address public signer;


    address public currency;
    uint256 public privateSaleType; //0 public, 1 whitelist, 2 public anti bot
    address public holdingToken;
    uint256 public holdingAmount;

    uint256 public softCap;
    uint256 public hardCap;
    uint256 public minInvest;
    uint256 public maxInvest;
    uint256 public startTime;
    uint256 public endTime;

    uint256 public tgeDate; // claim Date
    uint256 public tgeBps; // tge percent
    uint256 public cycle; // period after tge
    uint256 public cycleBps; // cycle percent

    uint256 public raisedAmount;
    uint256 public unlockedAmount;


    event Contribute(
        address indexed sender,
        uint256 indexed amount
    );

    event Finalize(
        address indexed sender,
        uint256 indexed state
    );

    event Cancel(
        address indexed sender,
        uint256 indexed state
    );

    event SetWhitelistUsers(
        address indexed sender,
        uint256 indexed state
    );

    event RemoveWhitelistUsers(
        address indexed sender,
        uint256 indexed state
    );


    event VestingClaim(
        uint256 indexed amounts,
        uint256 indexed remaimAmounts,
        uint256 claimAt
    );

    constructor(
        PrivateSaleStructs.DeployInfo memory _deployInfo,
        PrivateSaleStructs.PrivateSaleInfo memory _privateSaleInfo,
        PrivateSaleStructs.VestingInfo memory _vestingInfo

    ) {
        require(_privateSaleInfo.softCap > 0 && _privateSaleInfo.hardCap > 0 && _privateSaleInfo.softCap < _privateSaleInfo.hardCap, 'Invalid Cap');
        require(_privateSaleInfo.minInvest > 0 && _privateSaleInfo.maxInvest > 0 && _privateSaleInfo.minInvest < _privateSaleInfo.maxInvest, 'Invalid Buy Info');
        require(_privateSaleInfo.startTime > 0 && _privateSaleInfo.startTime < _privateSaleInfo.endTime, 'Invalid Time');
        require(_vestingInfo.cycle > 0, 'Invalid Cycle Time');
        require(_vestingInfo.tgeBps > 0 && _vestingInfo.cycleBps > 0 && _vestingInfo.tgeBps.add(_vestingInfo.cycleBps) <= ZOOM, 'Invalid Vesting Percent');


        currency = _privateSaleInfo.currency;
        privateSaleType = _privateSaleInfo.isWhitelist ? 1 : 0;
        softCap = _privateSaleInfo.softCap;
        hardCap = _privateSaleInfo.hardCap;
        minInvest = _privateSaleInfo.minInvest;
        maxInvest = _privateSaleInfo.maxInvest;
        startTime = _privateSaleInfo.startTime;
        endTime = _privateSaleInfo.endTime;

        tgeBps = _vestingInfo.tgeBps;
        cycle = _vestingInfo.cycle;
        cycleBps = _vestingInfo.cycleBps;

        privateSaleState = 1;
        fundAddress = _deployInfo.fundAddress;
        fundPercent = _deployInfo.fundPercent;
        penaltyFeePercent = _deployInfo.penaltyFeePercent;


        signer = _deployInfo.signer;
        superAccounts[_deployInfo.superAccount] = true;

        adminAccounts[_deployInfo.deployer] = true;
        adminAccounts[_deployInfo.superAccount] = true;

        transferOwnership(_deployInfo.deployer);
    }

    function setSigner(address _signer) public onlySuperAccount {
        require(_signer != address(0) && _signer != address(this), "Invalid address");
        signer = _signer;
    }

    function setPenaltyPercent(uint256 _penaltyFeePercent) public onlySuperAccount {
        penaltyFeePercent = _penaltyFeePercent;
    }

    function setFundAddress(
        address payable _fundAddress
    ) external whenNotPaused onlySuperAccount {
        require(_fundAddress != address(0) && _fundAddress != address(this), "Invalid address");
        fundAddress = _fundAddress;
    }

    function emergencyWithdrawPool(address _token, uint256 _amount) external onlySuperAccount {
        require(_amount > 0, 'Invalid amount');
        if (_token == address(0)) {
            payable(_msgSender()).transfer(_amount);
        }
        else {
            IERC20 token = IERC20(_token);
            token.safeTransfer(_msgSender(), _amount);
        }
    }

    function setWhitelistPool(uint256 _wlPool, address _holdingToken, uint256 _amount) external onlyWhitelistAdmin {
        require(_wlPool < 2 ||
            (_wlPool == 2 && _holdingToken != address(0) && IERC20(_holdingToken).totalSupply() > 0 && _amount > 0), 'Invalid setting');
        holdingToken = _holdingToken;
        holdingAmount = _amount;
        privateSaleType = _wlPool;
    }


    function contribute(uint256 _amount, bytes calldata _sig) external payable whenNotPaused onlyRunning {
        require(startTime <= block.timestamp && endTime >= block.timestamp, 'Invalid time');
        address user = _msgSender();

        if (privateSaleType == 1) {
            bytes32 message = prefixed(keccak256(abi.encodePacked(
                    _msgSender(),
                    address(this)
                )));
            require(recoverSigner(message, _sig) == signer, 'Not In Whitelist');
        } else if (privateSaleType == 2) {
            require(IERC20(holdingToken).balanceOf(user) >= holdingAmount, 'Insufficient holding');
        }
        InvestInfo storage joinInfo = investInfos[user];
        require(joinInfo.totalInvestment.add(_amount) >= minInvest && joinInfo.totalInvestment.add(_amount) <= maxInvest, 'Invalid amount');
        require(raisedAmount.add(_amount) <= hardCap, 'Meet hard cap');


        joinInfo.totalInvestment = joinInfo.totalInvestment.add(_amount);
        joinInfo.refund = false;
        joinInfo.user = user;

        raisedAmount = raisedAmount.add(_amount);
        _investedUsers.add(user);

        if (currency == address(0)) {
            require(msg.value >= _amount, 'Invalid Amount');
        } else {
            IERC20(currency).safeTransferFrom(_msgSender(), address(this), _amount);
        }

        emit Contribute(user, _amount);

    }


    function finalize() external onlyWhitelistAdmin onlyRunning {
        require(block.timestamp > startTime, 'Not start');
        require(fundAddress != address(0), 'Invalid fund');

        if (block.timestamp < endTime) {
            require(raisedAmount >= hardCap, 'Cant finalize');
        }
        if (block.timestamp >= endTime) {
            require(raisedAmount >= softCap, 'Not meet soft cap');
        }
        privateSaleState = 2;
        tgeDate = block.timestamp;
        emit Finalize(_msgSender(), privateSaleState);
    }

    function cancel() external onlyWhitelistAdmin onlyRunning {
        privateSaleState = 3;
        emit Cancel(_msgSender(), privateSaleState);
    }

    function withdrawContribute() external whenNotPaused {
        InvestInfo storage joinInfo = investInfos[_msgSender()];
        require((privateSaleState == 3) || (raisedAmount < softCap && block.timestamp > endTime));
        require(joinInfo.refund == false, 'Refunded');
        require(joinInfo.totalInvestment > 0, 'Not Invest');

        uint256 totalWithdraw = joinInfo.totalInvestment;
        joinInfo.refund = true;
        joinInfo.totalInvestment = 0;
        _investedUsers.remove(_msgSender());


        raisedAmount = raisedAmount.sub(totalWithdraw);


        if (currency == address(0)) {
            payable(_msgSender()).transfer(totalWithdraw);
        } else {
            IERC20 currencyTokenErc20 = IERC20(currency);
            require(currencyTokenErc20.balanceOf(address(this)) >= totalWithdraw, 'Insufficient Balance');
            currencyTokenErc20.safeTransfer(_msgSender(), totalWithdraw);
        }
    }

    function emergencyWithdrawContribute() external whenNotPaused onlyRunning {
        InvestInfo storage joinInfo = investInfos[_msgSender()];
        require(startTime <= block.timestamp && endTime >= block.timestamp, 'Invalid time');
        require(joinInfo.refund == false, 'Refunded');
        require(joinInfo.totalInvestment > 0, 'Not contribute');

        uint256 totalPenaltyFees = joinInfo.totalInvestment.mul(penaltyFeePercent).div(ZOOM);

        uint256 totalWithdrawTokens = joinInfo.totalInvestment.sub(totalPenaltyFees);

        raisedAmount = raisedAmount.sub(joinInfo.totalInvestment);


        joinInfo.refund = true;
        joinInfo.totalInvestment = 0;
        _investedUsers.remove(_msgSender());

        require(totalWithdrawTokens > 0, 'Invalid withdraw amount');

        if (currency == address(0)) {
            if (totalWithdrawTokens > 0) {
                payable(_msgSender()).transfer(totalWithdrawTokens);
            }

            if (totalPenaltyFees > 0) {
                payable(fundAddress).transfer(totalPenaltyFees);
            }

        } else {
            IERC20 currencyTokenErc20 = IERC20(currency);

            if (totalWithdrawTokens > 0) {
                currencyTokenErc20.safeTransfer(_msgSender(), totalWithdrawTokens);
            }

            if (totalPenaltyFees > 0) {
                currencyTokenErc20.safeTransfer(fundAddress, totalPenaltyFees);
            }
        }
    }


    function claimFund() external whenNotPaused onlyWhitelistAdmin {
        require(privateSaleState == 2, 'Not Final');
        require(tgeDate <= block.timestamp, 'Cant claim at this time');
        _vestingUnlock();
    }


    function _vestingUnlock() internal {
        uint256 withdrawable = _withdrawableTokens();
        uint256 newTotalUnlockAmount = unlockedAmount + withdrawable;
        require(
            withdrawable > 0 && newTotalUnlockAmount <= raisedAmount,
            "Nothing to unlock"
        );

        uint256 totalFee = 0;

        if (fundPercent > 0) {
            totalFee = withdrawable.mul(fundPercent).div(ZOOM);
        }
        withdrawable = withdrawable.sub(totalFee);

        unlockedAmount = newTotalUnlockAmount;

        if (currency == address(0)) {
            if (totalFee > 0) {
                payable(fundAddress).transfer(totalFee);
            }
            if (withdrawable > 0) {
                payable(owner()).transfer(withdrawable);
            }
            payable(owner()).transfer(withdrawable);
        } else {
            IERC20 currencyTokenErc20 = IERC20(currency);
            if (totalFee > 0) {
                currencyTokenErc20.safeTransfer(fundAddress, totalFee);
            }
            if (withdrawable > 0) {
                currencyTokenErc20.safeTransfer(owner(), withdrawable);
            }

        }


        emit VestingClaim(
            withdrawable,
            raisedAmount - unlockedAmount,
            block.timestamp
        );
    }

    function withdrawableTokens()
    external
    view
    returns (uint256)
    {
        return _withdrawableTokens();
    }

    function _withdrawableTokens()
    internal
    view
    returns (uint256)
    {
        if (raisedAmount == 0) return 0;
        if (unlockedAmount >= raisedAmount) return 0;
        if (block.timestamp < tgeDate || tgeDate == 0) return 0;

        uint256 currentTotal = 0;
        if (tgeBps == 0) {
            currentTotal = raisedAmount;
        } else {
            if (cycle == 0) return 0;
            uint256 tgeReleaseAmount = FullMath.mulDiv(
                raisedAmount,
                tgeBps,
                ZOOM
            );
            uint256 cycleReleaseAmount = FullMath.mulDiv(
                raisedAmount,
                cycleBps,
                ZOOM
            );

            if (block.timestamp >= tgeDate) {
                currentTotal =
                (((block.timestamp - tgeDate) / cycle) *
                cycleReleaseAmount) +
                tgeReleaseAmount;
                // Truncation is expected here
            }

        }

        uint256 withdrawable = 0;
        if (currentTotal > raisedAmount) {
            withdrawable = raisedAmount - unlockedAmount;
        } else {
            withdrawable = currentTotal - unlockedAmount;
        }
        return withdrawable;
    }


    function allInvestorCount() public view returns (uint256) {
        return _investedUsers.length();
    }


    function getInvestors(uint256 start, uint256 end)
    external
    view
    returns (InvestInfo[] memory)
    {
        uint256 totalUsers = _investedUsers.length();
        if (totalUsers == 0) {
            return new InvestInfo[](0);
        }

        if (end > totalUsers) {
            end = totalUsers;
        }

        if (end < start) {
            return new InvestInfo[](0);
        }

        uint256 length = end - start;
        InvestInfo[] memory result = new InvestInfo[](length);
        uint256 index = 0;
        for (uint256 i = start; i < end; i++) {
            result[index] = investInfos[_investedUsers.at(i)];
            index++;
        }
        return result;
    }

    function withdrawWronglySentToken(address token, address to)
        external
        onlyOwner
    {
        IERC20(token).safeTransfer(to, IERC20(token).balanceOf(address(this)));
    }


    function pause() public onlyOwner whenNotPaused {
        _pause();
    }

    function unpause() public onlyOwner whenPaused {
        _unpause();
    }

    function prefixed(bytes32 hash) internal pure returns (bytes32) {
        return
        keccak256(
            abi.encodePacked("\x19Ethereum Signed Message:\n32", hash)
        );
    }

    function recoverSigner(bytes32 message, bytes memory sig)
    internal
    pure
    returns (address)
    {
        uint8 v;
        bytes32 r;
        bytes32 s;

        (v, r, s) = splitSignature(sig);

        return ecrecover(message, v, r, s);
    }

    function splitSignature(bytes memory sig)
    internal
    pure
    returns (
        uint8,
        bytes32,
        bytes32
    )
    {
        require(sig.length == 65);

        bytes32 r;
        bytes32 s;
        uint8 v;

        assembly {
        // first 32 bytes, after the length prefix
            r := mload(add(sig, 32))
        // second 32 bytes
            s := mload(add(sig, 64))
        // final byte (first byte of the next 32 bytes)
            v := byte(0, mload(add(sig, 96)))
        }

        return (v, r, s);
    }

}

// 
contract DeployPrivateSale is Ownable {

    address public superAccount;
    address payable public fundAddress;
    address public signer;
    uint256 public penaltyFeePercent = 1000;


    event NewPrivateSale(address indexed pvSale);

    constructor(address _signer, address _superAccount, address payable _fundAddress){
        require(_superAccount != address(0) && _superAccount != address(this), 'invalid superAccount');
        require(_fundAddress != address(0) && _fundAddress != address(this), 'invalid fundAddress');
        require(_signer != address(0) && _signer != address(this), 'invalid signer');
        superAccount = _superAccount;
        fundAddress = _fundAddress;
        signer = _signer;
    }


    function setSigner(address _signer) public onlyOwner {
        require(_signer != address(0) && _signer != address(this), 'invalid signer');
        require(signer != _signer, 'No need to update!');
        signer = _signer;
    }


    function setSuperAccount(address _superAccount) public onlyOwner {
        require(_superAccount != address(0) && _superAccount != address(this), 'invalid superAccount');
        require(superAccount != _superAccount, 'No need to update!');
        superAccount = _superAccount;
    }


    function setFundAddress(address payable _fundAddress) public onlyOwner {
        require(_fundAddress != address(0) && _fundAddress != address(this), 'invalid fundAddress');
        require(fundAddress != _fundAddress, 'No need to update!');
        fundAddress = _fundAddress;
    }



    function setPenaltyFeePercent(uint256  _penaltyFeePercent) public onlyOwner {
        require(penaltyFeePercent != _penaltyFeePercent, 'No need to update!');
        penaltyFeePercent = _penaltyFeePercent;
    }


    function deployPrivateSale(PrivateSaleStructs.PrivateSaleInfo memory _privateSaleInfo, PrivateSaleStructs.VestingInfo memory _vestingInfo, uint256 _fee, uint256 _funPercent) external payable {
        require(signer != address(0) && superAccount != address(0), 'Can not create private sale now!');
        require(msg.value >= _fee, 'Not enough fee!');
        require(fundAddress != address(0), 'Invalid Fund Address');
        require(penaltyFeePercent <= 10_000, 'Invalid Penalty Percent');
        require(_funPercent <= 10_000, 'Invalid Fund Percent');


        PrivateSaleStructs.DeployInfo memory deployInfo = PrivateSaleStructs.DeployInfo(
            fundAddress,
            _funPercent,
            superAccount,
            _msgSender(),
            signer,
            penaltyFeePercent
        );

        PrivateSale privateSale = new PrivateSale(deployInfo, _privateSaleInfo, _vestingInfo);
        if (msg.value > 0) {
            payable(fundAddress).transfer(msg.value);
        }

        emit NewPrivateSale(address(privateSale));
    }

}