#!/usr/bin/env python2

# Steven Herbst
# sherbst@stanford.edu
#
# CS448H Winter 2017

# Code to expand generate a Digikey BOM

import argparse
import json
import collections
import requests
import re
from bs4 import BeautifulSoup

def main():
    # load command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--json')
    parser.add_argument('--bom')
    parser.add_argument('--qty', type=int, default=1)
    args = parser.parse_args()

    # read board placement from SMT-PCB
    with open(args.json, 'r') as f:
        json_dict = json.load(f)

    # add quantity information
    json_dict['quantity'] = args.qty

    # write back updated JSON file
    with open(args.json, 'w') as f:
        json.dump(json_dict, f, indent=2, sort_keys=True)

    # get module_dict from JSON file
    module_dict = json_dict['module_dict']

    # count up the total number needed of each part
    def def_dict_gen():
        return {'qty': 0, 'refset': set()}
    mpn_dict = collections.defaultdict(def_dict_gen)
    for name, module in module_dict.items():
        partnos = module['partno']
        if not partnos:
            continue
        if not isinstance(partnos, list):
            partnos = [partnos]
        for partno in partnos:
            mpn_dict[partno]['qty'] = mpn_dict[partno]['qty'] + args.qty
            mpn_dict[partno]['refset'].add(name)

    # resolve MPNs to Digikey part numbers
    bom_dict = remap_dict(resolve_mpn, mpn_dict)

    with open(args.bom, 'w') as f:
        for partno, val in bom_dict.items():
            qty_str = str(val['qty'])
            refset_str = ','.join(val['refset'])
            row = '\t'.join([partno, qty_str, refset_str]) 
            f.write(row + '\n')

def resolve_mpn(mpn):
    print 'Resolving MPN:', mpn

    req = query_digikey(mpn)
    soup = BeautifulSoup(req.content, 'html.parser')

    productID = re.compile('product(id|ID)')
    res_list = soup.findAll('meta', {'itemprop': productID})

    if len(res_list) == 0:
        raise Exception('Part not found.')
    elif len(res_list) == 1:
        return sku(res_list[0])
    else:
        bestPrice = float('inf')
        bestSku = None
        for res in res_list:
            if minQty(res) == 1 and price(res) < bestPrice:
                bestPrice = price(res)
                bestSku = sku(res)
        return bestSku
            
def sku(res):
    return res['content'][4:]

def minQty(res):
    grandparent = res.parent.parent
    td = grandparent.find('td', {'class': 'tr-minQty'})
    val = td.get_text()
    val = val.strip()
    val = val.replace(',', '')
    try:
        val = int(val)
    except:
        val = float('inf')
    return val

def price(res):
    grandparent = res.parent.parent
    td = grandparent.find('td', {'class': 'tr-unitPrice'})
    val = td.get_text()
    val = val.strip()
    val = val.replace(',', '')
    try:
        val = float(val)
    except:
        val = float('inf')
    return val

def query_digikey(mpn):
    headers = { 'User-Agent' : 'Mozilla/5.0' }
    url = 'http://www.digikey.com/products/en?keywords='
    url = url + mpn
    req = requests.get(url, headers=headers)
    return req

def to_list(val):
    # convert single value to length-1 list
    if not isinstance(val, list):
        return [val]
    else:
        return val

def remap_dict(map_func, old_dict):
    new_dict = {}
    for old_key, val in old_dict.items():
        new_key = map_func(old_key)
        new_dict[new_key] = val

    return new_dict

if __name__ == '__main__':
    main()
