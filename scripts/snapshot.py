import json
import os
import math
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from functools import partial, wraps
from itertools import zip_longest
from pathlib import Path

import toml
from brownie import MerkleDistributor, Wei, accounts, interface, rpc, web3
from eth_abi import decode_single, encode_single
from eth_abi.packed import encode_abi_packed
from eth_utils import encode_hex
from toolz import valfilter, valmap
from tqdm import tqdm, trange
from click import secho

DISTRIBUTOR_ADDRESS = '0x5e37996bcfF8C169e77b00D7b6e7261bbC60761e'
ZERO_ADDRESS = '0x0000000000000000000000000000000000000000'
START_BLOCK = 11291458
SNAPSHOT_BLOCK = 11541218

coverAddress = '0x5D8d9F5b96f4438195BE9b99eee6118Ed4304286'
blacksmithAddress = '0xE0B94a7BB45dD905c79bB1992C9879f40F1CAeD5'
uniswapLPAddress = '0x465E22E30CE69eC81C2DeFA2C71D510875B31891'
sushiswapLPAddress = '0xe7689B2C21242e07870AAA0ffee1eC11833d5E24'

merkleABI = r'''[{"inputs":[{"internalType":"address","name":"token_","type":"address"},{"internalType":"bytes32","name":"merkleRoot_","type":"bytes32"}],"stateMutability":"nonpayable","type":"constructor"},{"anonymous":false,"inputs":[{"indexed":false,"internalType":"uint256","name":"index","type":"uint256"},{"indexed":false,"internalType":"address","name":"account","type":"address"},{"indexed":false,"internalType":"uint256","name":"amount","type":"uint256"}],"name":"Claimed","type":"event"},{"inputs":[{"internalType":"uint256","name":"index","type":"uint256"},{"internalType":"address","name":"account","type":"address"},{"internalType":"uint256","name":"amount","type":"uint256"},{"internalType":"bytes32[]","name":"merkleProof","type":"bytes32[]"},{"internalType":"uint256","name":"tipBips","type":"uint256"}],"name":"claim","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"_token","type":"address"},{"internalType":"uint256","name":"_amount","type":"uint256"}],"name":"collectDust","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"uint256","name":"index","type":"uint256"}],"name":"isClaimed","outputs":[{"internalType":"bool","name":"","type":"bool"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"merkleRoot","outputs":[{"internalType":"bytes32","name":"","type":"bytes32"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"token","outputs":[{"internalType":"address","name":"","type":"address"}],"stateMutability":"view","type":"function"}]'''
coverABI = r'''[{"inputs":[],"stateMutability":"nonpayable","type":"constructor"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"owner","type":"address"},{"indexed":true,"internalType":"address","name":"spender","type":"address"},{"indexed":false,"internalType":"uint256","name":"value","type":"uint256"}],"name":"Approval","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"previousOwner","type":"address"},{"indexed":true,"internalType":"address","name":"newOwner","type":"address"}],"name":"OwnershipTransferred","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"from","type":"address"},{"indexed":true,"internalType":"address","name":"to","type":"address"},{"indexed":false,"internalType":"uint256","name":"value","type":"uint256"}],"name":"Transfer","type":"event"},{"inputs":[],"name":"START_TIME","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"owner","type":"address"},{"internalType":"address","name":"spender","type":"address"}],"name":"allowance","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"spender","type":"address"},{"internalType":"uint256","name":"amount","type":"uint256"}],"name":"approve","outputs":[{"internalType":"bool","name":"","type":"bool"}],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"account","type":"address"}],"name":"balanceOf","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"blacksmith","outputs":[{"internalType":"address","name":"","type":"address"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"decimals","outputs":[{"internalType":"uint8","name":"","type":"uint8"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"spender","type":"address"},{"internalType":"uint256","name":"subtractedValue","type":"uint256"}],"name":"decreaseAllowance","outputs":[{"internalType":"bool","name":"","type":"bool"}],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"spender","type":"address"},{"internalType":"uint256","name":"addedValue","type":"uint256"}],"name":"increaseAllowance","outputs":[{"internalType":"bool","name":"","type":"bool"}],"stateMutability":"nonpayable","type":"function"},{"inputs":[],"name":"migrator","outputs":[{"internalType":"address","name":"","type":"address"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"_account","type":"address"},{"internalType":"uint256","name":"_amount","type":"uint256"}],"name":"mint","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[],"name":"name","outputs":[{"internalType":"string","name":"","type":"string"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"owner","outputs":[{"internalType":"address","name":"","type":"address"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"_treasury","type":"address"},{"internalType":"address","name":"_vestor","type":"address"},{"internalType":"address","name":"_blacksmith","type":"address"},{"internalType":"address","name":"_migrator","type":"address"}],"name":"release","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"_newBlacksmith","type":"address"}],"name":"setBlacksmith","outputs":[{"internalType":"bool","name":"","type":"bool"}],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"_newMigrator","type":"address"}],"name":"setMigrator","outputs":[{"internalType":"bool","name":"","type":"bool"}],"stateMutability":"nonpayable","type":"function"},{"inputs":[],"name":"symbol","outputs":[{"internalType":"string","name":"","type":"string"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"totalSupply","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"recipient","type":"address"},{"internalType":"uint256","name":"amount","type":"uint256"}],"name":"transfer","outputs":[{"internalType":"bool","name":"","type":"bool"}],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"sender","type":"address"},{"internalType":"address","name":"recipient","type":"address"},{"internalType":"uint256","name":"amount","type":"uint256"}],"name":"transferFrom","outputs":[{"internalType":"bool","name":"","type":"bool"}],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"newOwner","type":"address"}],"name":"transferOwnership","outputs":[],"stateMutability":"nonpayable","type":"function"}]'''
pairABI = r'''[{"inputs":[],"payable":false,"stateMutability":"nonpayable","type":"constructor"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"owner","type":"address"},{"indexed":true,"internalType":"address","name":"spender","type":"address"},{"indexed":false,"internalType":"uint256","name":"value","type":"uint256"}],"name":"Approval","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"sender","type":"address"},{"indexed":false,"internalType":"uint256","name":"amount0","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"amount1","type":"uint256"},{"indexed":true,"internalType":"address","name":"to","type":"address"}],"name":"Burn","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"sender","type":"address"},{"indexed":false,"internalType":"uint256","name":"amount0","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"amount1","type":"uint256"}],"name":"Mint","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"sender","type":"address"},{"indexed":false,"internalType":"uint256","name":"amount0In","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"amount1In","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"amount0Out","type":"uint256"},{"indexed":false,"internalType":"uint256","name":"amount1Out","type":"uint256"},{"indexed":true,"internalType":"address","name":"to","type":"address"}],"name":"Swap","type":"event"},{"anonymous":false,"inputs":[{"indexed":false,"internalType":"uint112","name":"reserve0","type":"uint112"},{"indexed":false,"internalType":"uint112","name":"reserve1","type":"uint112"}],"name":"Sync","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"from","type":"address"},{"indexed":true,"internalType":"address","name":"to","type":"address"},{"indexed":false,"internalType":"uint256","name":"value","type":"uint256"}],"name":"Transfer","type":"event"},{"constant":true,"inputs":[],"name":"DOMAIN_SEPARATOR","outputs":[{"internalType":"bytes32","name":"","type":"bytes32"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"MINIMUM_LIQUIDITY","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"PERMIT_TYPEHASH","outputs":[{"internalType":"bytes32","name":"","type":"bytes32"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"","type":"address"},{"internalType":"address","name":"","type":"address"}],"name":"allowance","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"spender","type":"address"},{"internalType":"uint256","name":"value","type":"uint256"}],"name":"approve","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"","type":"address"}],"name":"balanceOf","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"to","type":"address"}],"name":"burn","outputs":[{"internalType":"uint256","name":"amount0","type":"uint256"},{"internalType":"uint256","name":"amount1","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"decimals","outputs":[{"internalType":"uint8","name":"","type":"uint8"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"factory","outputs":[{"internalType":"address","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"getReserves","outputs":[{"internalType":"uint112","name":"_reserve0","type":"uint112"},{"internalType":"uint112","name":"_reserve1","type":"uint112"},{"internalType":"uint32","name":"_blockTimestampLast","type":"uint32"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"_token0","type":"address"},{"internalType":"address","name":"_token1","type":"address"}],"name":"initialize","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"kLast","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"to","type":"address"}],"name":"mint","outputs":[{"internalType":"uint256","name":"liquidity","type":"uint256"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"name","outputs":[{"internalType":"string","name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[{"internalType":"address","name":"","type":"address"}],"name":"nonces","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"owner","type":"address"},{"internalType":"address","name":"spender","type":"address"},{"internalType":"uint256","name":"value","type":"uint256"},{"internalType":"uint256","name":"deadline","type":"uint256"},{"internalType":"uint8","name":"v","type":"uint8"},{"internalType":"bytes32","name":"r","type":"bytes32"},{"internalType":"bytes32","name":"s","type":"bytes32"}],"name":"permit","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"price0CumulativeLast","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"price1CumulativeLast","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"to","type":"address"}],"name":"skim","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"uint256","name":"amount0Out","type":"uint256"},{"internalType":"uint256","name":"amount1Out","type":"uint256"},{"internalType":"address","name":"to","type":"address"},{"internalType":"bytes","name":"data","type":"bytes"}],"name":"swap","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"symbol","outputs":[{"internalType":"string","name":"","type":"string"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[],"name":"sync","outputs":[],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":true,"inputs":[],"name":"token0","outputs":[{"internalType":"address","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"token1","outputs":[{"internalType":"address","name":"","type":"address"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":true,"inputs":[],"name":"totalSupply","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"payable":false,"stateMutability":"view","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"to","type":"address"},{"internalType":"uint256","name":"value","type":"uint256"}],"name":"transfer","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"},{"constant":false,"inputs":[{"internalType":"address","name":"from","type":"address"},{"internalType":"address","name":"to","type":"address"},{"internalType":"uint256","name":"value","type":"uint256"}],"name":"transferFrom","outputs":[{"internalType":"bool","name":"","type":"bool"}],"payable":false,"stateMutability":"nonpayable","type":"function"}]'''
blacksmithABI = r'''[{"inputs":[{"internalType":"address","name":"_coverAddress","type":"address"},{"internalType":"address","name":"_governance","type":"address"},{"internalType":"address","name":"_treasury","type":"address"}],"stateMutability":"nonpayable","type":"constructor"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"miner","type":"address"},{"indexed":true,"internalType":"address","name":"lpToken","type":"address"},{"indexed":false,"internalType":"uint256","name":"amount","type":"uint256"}],"name":"Deposit","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"previousOwner","type":"address"},{"indexed":true,"internalType":"address","name":"newOwner","type":"address"}],"name":"OwnershipTransferred","type":"event"},{"anonymous":false,"inputs":[{"indexed":true,"internalType":"address","name":"miner","type":"address"},{"indexed":true,"internalType":"address","name":"lpToken","type":"address"},{"indexed":false,"internalType":"uint256","name":"amount","type":"uint256"}],"name":"Withdraw","type":"event"},{"inputs":[],"name":"START_TIME","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"WEEK","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"_lpToken","type":"address"},{"internalType":"address","name":"_bonusToken","type":"address"},{"internalType":"uint256","name":"_startTime","type":"uint256"},{"internalType":"uint256","name":"_endTime","type":"uint256"},{"internalType":"uint256","name":"_totalBonus","type":"uint256"}],"name":"addBonusToken","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"_lpToken","type":"address"},{"internalType":"uint256","name":"_weight","type":"uint256"}],"name":"addPool","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address[]","name":"_lpTokens","type":"address[]"},{"internalType":"uint256[]","name":"_weights","type":"uint256[]"}],"name":"addPools","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"","type":"address"}],"name":"allowBonusTokens","outputs":[{"internalType":"uint8","name":"","type":"uint8"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"","type":"address"}],"name":"bonusTokens","outputs":[{"internalType":"address","name":"addr","type":"address"},{"internalType":"uint256","name":"startTime","type":"uint256"},{"internalType":"uint256","name":"endTime","type":"uint256"},{"internalType":"uint256","name":"totalBonus","type":"uint256"},{"internalType":"uint256","name":"accBonusPerToken","type":"uint256"},{"internalType":"uint256","name":"lastUpdatedAt","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"_lpToken","type":"address"}],"name":"claimRewards","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address[]","name":"_lpTokens","type":"address[]"}],"name":"claimRewardsForPools","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"_lpToken","type":"address"}],"name":"collectBonusDust","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"_token","type":"address"}],"name":"collectDust","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[],"name":"cover","outputs":[{"internalType":"contract ICOVER","name":"","type":"address"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"_lpToken","type":"address"},{"internalType":"uint256","name":"_amount","type":"uint256"}],"name":"deposit","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"_lpToken","type":"address"}],"name":"emergencyWithdraw","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[],"name":"getPoolList","outputs":[{"internalType":"address[]","name":"","type":"address[]"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"governance","outputs":[{"internalType":"address","name":"","type":"address"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"","type":"address"},{"internalType":"address","name":"","type":"address"}],"name":"miners","outputs":[{"internalType":"uint256","name":"amount","type":"uint256"},{"internalType":"uint256","name":"rewardWriteoff","type":"uint256"},{"internalType":"uint256","name":"bonusWriteoff","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"owner","outputs":[{"internalType":"address","name":"","type":"address"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"uint256","name":"","type":"uint256"}],"name":"poolList","outputs":[{"internalType":"address","name":"","type":"address"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"","type":"address"}],"name":"pools","outputs":[{"internalType":"uint256","name":"weight","type":"uint256"},{"internalType":"uint256","name":"accRewardsPerToken","type":"uint256"},{"internalType":"uint256","name":"lastUpdatedAt","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"totalWeight","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"_newAddress","type":"address"}],"name":"transferMintingRights","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"newOwner","type":"address"}],"name":"transferOwnership","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[],"name":"treasury","outputs":[{"internalType":"address","name":"","type":"address"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"_bonusToken","type":"address"},{"internalType":"uint8","name":"_status","type":"uint8"}],"name":"updateBonusTokenStatus","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"_lpToken","type":"address"}],"name":"updatePool","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address[]","name":"_lpTokens","type":"address[]"},{"internalType":"uint256[]","name":"_weights","type":"uint256[]"}],"name":"updatePoolWeights","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"uint256","name":"_start","type":"uint256"},{"internalType":"uint256","name":"_end","type":"uint256"}],"name":"updatePools","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"uint256","name":"_weeklyTotal","type":"uint256"}],"name":"updateWeeklyTotal","outputs":[],"stateMutability":"nonpayable","type":"function"},{"inputs":[{"internalType":"address","name":"_lpToken","type":"address"},{"internalType":"address","name":"_miner","type":"address"}],"name":"viewMined","outputs":[{"internalType":"uint256","name":"_minedCOVER","type":"uint256"},{"internalType":"uint256","name":"_minedBonus","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[],"name":"weeklyTotal","outputs":[{"internalType":"uint256","name":"","type":"uint256"}],"stateMutability":"view","type":"function"},{"inputs":[{"internalType":"address","name":"_lpToken","type":"address"},{"internalType":"uint256","name":"_amount","type":"uint256"}],"name":"withdraw","outputs":[],"stateMutability":"nonpayable","type":"function"}]'''

def cached(path):
    path = Path(path)
    codec = {'.toml': toml, '.json': json}[path.suffix]
    codec_args = {'.json': {'indent': 2}}.get(path.suffix, {})

    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            if path.exists():
                print('load from cache', path)
                return codec.loads(path.read_text())
            else:
                result = func(*args, **kwargs)
                os.makedirs(path.parent, exist_ok=True)
                path.write_text(codec.dumps(result, **codec_args))
                print('write to cache', path)
                return result

        return wrapper

    return decorator

# Get cover holders
def get_cover_holders():
    holders = Counter()
    contract = web3.eth.contract(coverAddress, abi=coverABI)
    for start in trange(START_BLOCK, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            holders[log['args']['from']] -= log['args']['value']
            holders[log['args']['to']] += log['args']['value']

    filteredHolders = valfilter(bool, dict(holders.most_common()))
    print(len(filteredHolders))

    return filteredHolders

# Get Uni LP holders
def get_uni_lp():
    holders = Counter()
    contract = web3.eth.contract(uniswapLPAddress, abi=pairABI)
    for start in trange(START_BLOCK, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            holders[log['args']['from']] -= log['args']['value']
            holders[log['args']['to']] += log['args']['value']

    filteredHolders = valfilter(bool, dict(holders.most_common()))
    print(len(filteredHolders))

    return filteredHolders

# Get SLP holders
def get_sushi_lp():
    holders = Counter()
    contract = web3.eth.contract(sushiswapLPAddress, abi=pairABI)
    for start in trange(START_BLOCK, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Transfer().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            holders[log['args']['from']] -= log['args']['value']
            holders[log['args']['to']] += log['args']['value']

    filteredHolders = valfilter(bool, dict(holders.most_common()))
    print(len(filteredHolders))

    return filteredHolders

# Get SLP staked in blacksmith
def get_blacksmith():
    holders = Counter()
    contract = web3.eth.contract(blacksmithAddress, abi=blacksmithABI)
    for start in trange(START_BLOCK, SNAPSHOT_BLOCK, 1000):
        end = min(start + 999, SNAPSHOT_BLOCK)
        logs = contract.events.Deposit().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            if log['args']['lpToken'] == sushiswapLPAddress:
                holders[log['args']['miner']] += log['args']['amount']

        logs = contract.events.Withdraw().getLogs(fromBlock=start, toBlock=end)
        for log in logs:
            if log['args']['lpToken'] == sushiswapLPAddress:
                holders[log['args']['miner']] -= log['args']['amount']

    filteredHolders = valfilter(bool, dict(holders.most_common()))
    print(len(filteredHolders))

    return filteredHolders

class MerkleTree:
    def __init__(self, elements):
        self.elements = sorted(set(web3.keccak(hexstr=el) for el in elements))
        self.layers = MerkleTree.get_layers(self.elements)

    @property
    def root(self):
        return self.layers[-1][0]

    def get_proof(self, el):
        el = web3.keccak(hexstr=el)
        idx = self.elements.index(el)
        proof = []
        for layer in self.layers:
            pair_idx = idx + 1 if idx % 2 == 0 else idx - 1
            if pair_idx < len(layer):
                proof.append(encode_hex(layer[pair_idx]))
            idx //= 2
        return proof

    @staticmethod
    def get_layers(elements):
        layers = [elements]
        while len(layers[-1]) > 1:
            layers.append(MerkleTree.get_next_layer(layers[-1]))
        return layers

    @staticmethod
    def get_next_layer(elements):
        return [MerkleTree.combined_hash(a, b) for a, b in zip_longest(elements[::2], elements[1::2])]

    @staticmethod
    def combined_hash(a, b):
        if a is None:
            return b
        if b is None:
            return a
        return web3.keccak(b''.join(sorted([a, b])))


@cached('snapshot/08-merkle-distribution.json')
def step_07(balances):
    elements = [(index, account, amount) for index, (account, amount) in enumerate(balances.items())]
    nodes = [encode_hex(encode_abi_packed(['uint', 'address', 'uint'], el)) for el in elements]
    tree = MerkleTree(nodes)
    distribution = {
        'merkleRoot': encode_hex(tree.root),
        'tokenTotal': hex(sum(balances.values())),
        'claims': {
            user: {'index': index, 'amount': hex(amount), 'proof': tree.get_proof(nodes[index])}
            for index, user, amount in elements
        },
    }
    print(f'merkle root: {encode_hex(tree.root)}')
    return distribution


def deploy():
    user = accounts[0] if rpc.is_active() else accounts.load(input('account: '))
    tree = json.load(open('snapshot/07-merkle-distribution.json'))
    root = tree['merkleRoot']
    token = str(DAI)
    MerkleDistributor.deploy(token, root, {'from': user})


def claim():
    claimer = accounts.load(input('Enter brownie account: '))
    dist = MerkleDistributor.at(DISTRIBUTOR_ADDRESS)
    tree = json.load(open('snapshot/07-merkle-distribution.json'))
    claim_other = input('Claim for another account? y/n [default: n] ') or 'n'
    assert claim_other in {'y', 'n'}
    user = str(claimer) if claim_other == 'n' else input('Enter address to claim for: ')

    if user not in tree['claims']:
        return secho(f'{user} is not included in the distribution', fg='red')
    claim = tree['claims'][user]
    if dist.isClaimed(claim['index']):
        return secho(f'{user} has already claimed', fg='yellow')

    amount = Wei(int(claim['amount'], 16)).to('ether')
    secho(f'Claimable amount: {amount} DAI', fg='green')
    if claim_other == 'n':  # no tipping for others
        secho(
            '\nThe return of funds to you was made possible by a team of volunteers who worked for free to make this happen.'
            '\nPlease consider tipping them a portion of your recovered funds as a way to say thank you.\n',
            fg='yellow',
        )
        tip = input('Enter tip amount in percent: ')
        tip = int(float(tip.rstrip('%')) * 100)
        assert 0 <= tip <= 10000, 'invalid tip amount'
    else:
        tip = 0

    tx = dist.claim(claim['index'], user, claim['amount'], claim['proof'], tip, {'from': claimer})
    tx.info()


def main():
    cover_holders = get_cover_holders()
    del cover_holders[ZERO_ADDRESS]

    uniswapCoverBal = cover_holders[uniswapLPAddress]
    print("Cover in uni", uniswapCoverBal)
    sushiswapCoverBal = cover_holders[sushiswapLPAddress]
    print("Cover in sushi", sushiswapCoverBal)

    total_supply = 0
    for key in cover_holders:
        total_supply += cover_holders[key]

    print("Total cover pre-exploit:", total_supply)

    del cover_holders[uniswapLPAddress] 
    del cover_holders[sushiswapLPAddress]

    with open('./snapshot/coverHolders.json', 'w') as fp:
        json.dump(cover_holders, fp)

    uni_holders = get_uni_lp()
    del uni_holders[ZERO_ADDRESS]

    with open('./snapshot/uniHolders.json', 'w') as fp:
        json.dump(uni_holders, fp)

    sushi_holders = get_sushi_lp()
    del sushi_holders[blacksmithAddress]
    del sushi_holders[ZERO_ADDRESS]

    with open('./snapshot/sushiHolders.json', 'w') as fp:
        json.dump(sushi_holders, fp)

    blacksmith = get_blacksmith()
    with open('./snapshot/blacksmith.json', 'w') as fp:
        json.dump(blacksmith, fp)

    total_sushi_holders = Counter(sushi_holders) + Counter(blacksmith)
    with open('./snapshot/totalSushiHolders.json', 'w') as fp:
        json.dump(total_sushi_holders, fp)

    baseSushiTotal = 0
    for key in sushi_holders:
        baseSushiTotal += sushi_holders[key]
    
    baseBlacksmithTotal = 0
    for key in blacksmith:
        baseBlacksmithTotal += blacksmith[key]

    sushiTotal = 0
    for key in total_sushi_holders:
        sushiTotal += total_sushi_holders[key]

    print("Total sushi:", sushiTotal)
    print("Total base sushi:", baseSushiTotal)
    print("Total base blacksmith:", baseBlacksmithTotal)

    # Normalize data for cover balances
    coverAllocation = Counter()
    total = 0
    for key in uni_holders:
        total += uni_holders[key]

    for key in uni_holders:
        coverAllocation[key] += (uni_holders[key] * uniswapCoverBal) / total

    total = 0
    for key in total_sushi_holders:
        total += total_sushi_holders[key]

    for key in total_sushi_holders:
        coverAllocation[key] += (total_sushi_holders[key] * sushiswapCoverBal) / total / 10**18

    total_cover = Counter(cover_holders) + Counter(coverAllocation)

    total_supply = 0
    for key in total_cover:
        total_supply += total_cover[key]

    print("Total cover after calcs:", total_supply)

    with open('./snapshot/finalCover.json', 'w') as fp:
        json.dump(total_cover, fp)

    # with open('./snapshot/final.json', 'w') as fp:
    #     json.dump(final, fp)
    # step_07(final)
