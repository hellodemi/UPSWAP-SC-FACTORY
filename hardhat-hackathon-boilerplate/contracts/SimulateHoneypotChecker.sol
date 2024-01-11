//
////SPDX-License-Identifier: MIT
//
//pragma abicoder v2;
//pragma solidity ^0.8.7;
//
//import "./interfaces/IBEP20.sol";
//import "./interfaces/IWETH.sol";
//import "./interfaces/IDEXRouter.sol";
//
//
//contract HoneyChecker {
//    IDEXRouter public router;
//    uint256 public approveMax =
//        115792089237316195423570985008687907853269984665640564039457584007913129639935;
//
//    uint256 public start_gasleft;
//    uint256 public finish_gasleft_buy;
//    uint256 public finish_gasleft_sell;
//
//    struct HoneyResponse {
//        uint256 buyResult;
//        uint256 expectedBuyAmount;
//        uint256 sellResult;
//        uint256 expectedAmountSell;
//        uint256 buyGasCost;
//        uint256 sellGasCost;
//    }
//
//    constructor() {}
//
//    function honeyCheck(address targetTokenAddress, address idexRouterAddres)
//        external
//        payable
//        returns (HoneyResponse memory response) {
//
//        router = IDEXRouter(idexRouterAddres);
//
//        IBEP20 wCoin = IBEP20(router.WETH());
//        IBEP20 targetToken = IBEP20(targetTokenAddress);
//
//        address[] memory buyPath = new address[](2);
//        buyPath[0] = router.WETH();
//        buyPath[1] = targetTokenAddress;
//
//        address[] memory sellPath = new address[](2);
//        sellPath[0] = targetTokenAddress;
//        sellPath[1] = router.WETH();
//
//        uint256[] memory amounts = router.getAmountsOut(msg.value, buyPath);
//
//        uint256 expectedBuyAmount = amounts[1];
//
//        IWETH(router.WETH()).deposit{value: msg.value}();
//
//        wCoin.approve(idexRouterAddres, approveMax);
//
//        uint256 startBuyGas = gasleft();
//        start_gasleft = startBuyGas;
//
//        router.swapExactTokensForTokensSupportingFeeOnTransferTokens(
//            msg.value,
//            1,
//            buyPath,
//            address(this),
//            block.timestamp + 10
//        );
//
//        uint256 buyResult = targetToken.balanceOf(address(this));
//
//        uint256 finishBuyGas = gasleft();
//        finish_gasleft_buy = finishBuyGas;
//
//        targetToken.approve(idexRouterAddres, approveMax);
//
//        uint256 startSellGas = gasleft();
//
//        router.swapExactTokensForTokensSupportingFeeOnTransferTokens(
//            buyResult,
//            1,
//            sellPath,
//            address(this),
//            block.timestamp + 10
//        );
//
//        uint256 finishSellGas = gasleft();
//        finish_gasleft_sell = finishSellGas;
//
//        uint256[] memory amountsSell = router.getAmountsOut(buyResult, sellPath);
//
//        uint256 expectedAmountSell = amountsSell[1];
//        uint256 actualSellResult = wCoin.balanceOf(address(this));
//
//        response = HoneyResponse(
//            buyResult,
//            expectedBuyAmount,
//            actualSellResult,
//            expectedAmountSell,
//            startBuyGas - finishBuyGas,
//            startSellGas - finishSellGas
//        );
//
//        return response;
//    }
//
//     function getAmountOutMin(address _tokenIn, address _tokenOut, uint256 _amountIn) internal view returns (uint256) {
//        address[] memory path;
//        if (_tokenIn == router.WETH() || _tokenOut == router.WETH()) {
//            path = new address[](2);
//            path[0] = _tokenIn;
//            path[1] = _tokenOut;
//        } else {
//            path = new address[](3);
//            path[0] = _tokenIn;
//            path[1] = router.WETH();
//            path[2] = _tokenOut;
//        }
//
//        uint256[] memory amountOutMins = router.getAmountsOut(_amountIn, path);
//        return amountOutMins[path.length -1];
//    }
//}
