import { Token, Pair } from './types';
export declare const exchanges: {
    Bithumb: {
        name: string;
        description: string;
        accounts: string[];
        logo: string;
        website: string;
    };
    OKEx: {
        name: string;
        description: string;
        accounts: string[];
        logo: string;
        website: string;
    };
    Bitfinex: {
        name: string;
        description: string;
        accounts: string[];
        logo: string;
        website: string;
    };
    'Gate.io': {
        name: string;
        description: string;
        accounts: string[];
        logo: string;
        website: string;
    };
    Kraken: {
        name: string;
        description: string;
        accounts: string[];
        logo: string;
        website: string;
    };
    Newdex: {
        name: string;
        description: string;
        accounts: string[];
        logo: string;
        website: string;
        linkGenerator: (token: Token, pair: Pair) => string;
    };
    DefiBox: {
        name: string;
        description: string;
        accounts: string[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, __: Pair) => string;
    };
    Chaince: {
        name: string;
        description: string;
        accounts: string[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, pair: Pair) => string;
    };
    Dexeos: {
        name: string;
        description: string;
        accounts: string[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, pair: Pair) => string;
    };
    Hoo: {
        name: string;
        description: string;
        accounts: string[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, pair: Pair) => string;
    };
    Whaleex: {
        name: string;
        description: string;
        accounts: string[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, pair: Pair) => string;
    };
    Chainrift: {
        name: string;
        description: string;
        accounts: never[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, pair: Pair) => string;
    };
    Eosdaq: {
        name: string;
        description: string;
        accounts: never[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, pair: Pair) => string;
    };
    BigONE: {
        name: string;
        description: string;
        accounts: never[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, pair: Pair) => string;
    };
    YOLO: {
        name: string;
        description: string;
        accounts: never[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, pair: Pair) => string;
    };
    Bancor: {
        name: string;
        description: string;
        accounts: never[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, pair: Pair) => string;
    };
    Alcor: {
        name: string;
        description: string;
        accounts: never[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, __: Pair) => string;
    };
    'Defis.Network': {
        name: string;
        description: string;
        accounts: never[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, __: Pair) => string;
    };
    DolphinSwap: {
        name: string;
        description: string;
        accounts: never[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, __: Pair) => string;
    };
    Proton: {
        name: string;
        description: string;
        accounts: never[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, __: Pair) => string;
    };
    Coingecko: {
        name: string;
        description: string;
        accounts: never[];
        logo: string;
        website: string;
        linkGenerator: (_: Token, __: Pair) => string;
    };
};
