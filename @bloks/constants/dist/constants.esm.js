var DEFAULT_SYMBOL = 'EOS';
var DEFAULT_SYSTEM_DOMAIN = 'eosio';
var DEFAULT_CHAIN = 'eos';

var getContractConstants = function getContractConstants(chain, systemDomain) {
  if (chain === void 0) {
    chain = DEFAULT_CHAIN;
  }

  if (systemDomain === void 0) {
    systemDomain = DEFAULT_SYSTEM_DOMAIN;
  }

  // Proxy Information Account
  var proxyInfo;

  if (['eos', 'bos', 'wax'].includes(chain)) {
    proxyInfo = 'regproxyinfo';
  } else if (chain === 'telos') {
    proxyInfo = 'tlsproxyinfo';
  }

  return {
    // Accounts
    EOSIO: systemDomain,
    EOSIO_TOKEN: !['fio', 'fio-test'].includes(chain) ? systemDomain + ".token" : 'fio.token',
    ACCOUNT_INFO: 'account.info',
    PROXY_INFO_ACCOUNT: proxyInfo,
    EOSIO_MSIG: systemDomain + ".msig",
    EOSIO_RAM: systemDomain + ".ram",
    EOSIO_STAKE: systemDomain + ".stake",
    EOSIO_PRODS: systemDomain + ".prods",
    EOSIO_NULL: systemDomain + ".null",
    EOSIO_RAMFEE: systemDomain + ".ramfee",
    EOSIO_VPAY: systemDomain + ".vpay",
    EOSIO_BPAY: systemDomain + ".bpay",
    EOSIO_REX: systemDomain + ".rex",
    // Params
    NEWACCOUNT_NAME_PARAM: chain.indexOf('bos') === -1 ? 'name' : 'newact',
    // Tables
    EOSIO_MSIG_APPROVALS_TABLE: 'approvals2',
    EOSIO_MSIG_PROPOSALS_TABLE: 'proposal',
    // Actions
    TRANSFER_ACTION: 'transfer',
    DELEGATE_BW_ACTION: 'delegatebw',
    UNDELEGATE_BW_ACTION: 'undelegatebw',
    VOTE_PRODUCER_ACTION: 'voteproducer',
    BUY_RAM_ACTION: 'buyram',
    BUY_RAM_BYTES_ACTION: 'buyrambyes',
    SELL_RAM_ACTION: 'sellram'
  };
};

var dapps = [{
  name: 'Alcor.exchange',
  description: 'The first self-listing DEX. With Alcor you can trade any EOS.IO tokens for system EOS tokens, atomically, without the participation of third parties! Create markets in one click, list your dapp token for one click, trade whatever you want.',
  shortDescription: 'The first self-listing DEX. With Alcor you can trade any EOS.IO tokens for system EOS tokens.',
  symbol: '',
  statistics: true,
  accounts: ['eostokensdex'],
  logo: 'https://i.ibb.co/dKDYDMc/vectorpaint.png',
  website: 'https://alcor.exchange/',
  app: 'https://alcor.exchange/',
  telegram: 'https://t.me/alcorexchange',
  medium: 'https://medium.com/@avral',
  twitter: 'https://twitter.com/avral_pro',
  github: 'https://github.com/avral/alcor-ui',
  chains: ['eos', 'wax', 'telos']
}, {
  name: 'SX',
  description: 'Building secure & reliable financial blockchain instruments',
  shortDescription: 'DeFi Swap & Flashloan',
  symbol: 'SX',
  accounts: ['swap.sx', 'vigor.sx', 'stable.sx', 'flash.sx', 'push.sx', 'network.sx', 'registry.sx', 'miner.sx', 'cross.sx', 'nav.sx', 'fee.sx', 'trade.sx', 'vaults.sx', 'proxy.sx', 'dust.sx', 'curve.sx'],
  logo: 'https://raw.githubusercontent.com/eoscafe/eos-airdrops/master/logos/sx.png',
  website: 'https://github.com/stableex',
  app: 'https://xnation.io',
  telegram: 'https://t.me/xnationio',
  medium: '',
  twitter: '',
  github: 'https://github.com/stableex',
  chains: ['eos']
}, {
  name: 'EOSNameService',
  description: 'EOS Name Service is the most comprehensive platform to register premium/base EOS/WAX account names.',
  shortDescription: 'EOS/WAX Name Service',
  symbol: '',
  partner: false,
  accounts: ['names'],
  logo: 'https://avatars1.githubusercontent.com/u/73891041',
  website: 'http://eosnameservice.io',
  app: 'http://eosnameservice.io',
  telegram: 'https://t.me/eosnameservice',
  medium: '',
  twitter: 'https://twitter.com/eosnameservice',
  github: 'https://github.com/eosnameservice',
  chains: ['eos', 'wax']
}, {
  name: 'Prospectors',
  description: 'Massive Multiplayer Online Real-Time Economic Strategy Game  MINE GOLD - BUILD YOUR WORLD',
  shortDescription: 'Massive Multiplayer Online Real-Time Economic Strategy Game',
  symbol: '',
  accounts: ['prospectorsc'],
  logo: 'https://bloks.io/img/dapps/prospectors.png',
  website: 'https://prospectors.io',
  app: 'https://prospectors.io',
  telegram: 'https://t.me/prospectorsgame',
  medium: 'https://medium.com/@prospectorsgame',
  twitter: 'https://twitter.com/prospectorsgame',
  github: 'https://github.com/prospectors/public/issues',
  chains: ['eos']
}, {
  name: 'APPICS',
  description: 'APPICS is the most engaged social media dApp that makes it easy to get rewarded with cryptocurrency for your social media activity like creating & curating content. The mobile interface is intuitive to use without any prior blockchain knowledge. Get rewarded for your passion!',
  shortDescription: 'APPICS is the most engaged social media dApp - earn APX Tokens for posting, commenting, and up-voting photos & videos!',
  symbol: 'APX',
  statistics: true,
  accounts: ['appicsappics'],
  logo: 'https://i.imgur.com/Ts9CNN5.png',
  website: 'https://appics.com',
  app: 'https://appics.com',
  telegram: 'https://t.me/appics_official',
  medium: 'https://medium.com/@appics',
  twitter: 'https://twitter.com/appics_official',
  github: 'https://github.com/phenom-company/appics_eos_token',
  chains: ['eos']
}, {
  name: 'Boid',
  description: 'Contribute your excess computing resources towards important causes while earning rewards. Join a team and rank up on the social leaderboards.',
  shortDescription: 'The Social Supercomputer. Contribute your excess computing resources towards important causes.',
  symbol: '',
  accounts: ['boidcomtoken', 'boidcompower', 'boidcommint1', 'boidcompromo'],
  logo: 'https://raw.githubusercontent.com/boid-com/assets/master/boidLogo-lg.png',
  website: 'https://boid.com',
  app: 'https://app.boid.com',
  telegram: 'https://t.me/Boidcom_official',
  medium: 'https://medium.com/@boidcom',
  twitter: 'https://twitter.com/boidcom',
  github: 'https://github.com/boid-com',
  chains: ['eos']
}, {
  name: 'The Billionaire Token',
  description: 'Most other coins or tokens have some sort of mining system. Billionaire Token has the exact opposite: It features a deflationary mechanism that destroys 30% of the gambled coins. Thus the tokens become more and more rare as more and more people gamble.',
  shortDescription: 'Billionaire Token has the opposite of a mining system: It features a deflationary mechanism that destroys 30% of the gambled coins.',
  symbol: 'XBL',
  accounts: ['billionairet', 'billionraffl', 'billionburnr', 'billionbot11', 'billionbot12', 'billionbot13', 'billionbot14'],
  app: 'https://BillionaireToken.com/',
  logo: 'https://BillionaireToken.com/images/logo_big.png',
  website: 'https://BillionaireToken.com/',
  telegram: 'https://t.me/BillionaireToken',
  medium: 'https://medium.com/@billionaire_3373',
  twitter: 'https://twitter.com/BillionaireTkn',
  github: 'https://github.com/BillionaireToken',
  chains: ['eos']
}, {
  name: 'Crypto Sword & Magic',
  description: 'Crypto Sword & Magic is the first blockbuster RPG on EOS blockchain, traditional turn-based RPG raising heroes to challenge new dungeons. Game assets are recorded on Blockchain and transactions run on smart contracts',
  shortDescription: 'Crypto Sword & Magic is the first blockbuster RPG on EOS blockchain.',
  symbol: 'CSM',
  accounts: ['swordnmagicm'],
  app: 'https://www.cryptoswordandmagic.com',
  logo: 'https://bloks.io/img/dapps/cryptosnm.png',
  website: 'https://www.cryptoswordandmagic.com',
  telegram: 'https://t.me/cryptosnm_comm_en',
  medium: 'https://medium.com/@cryptoswordandmagic',
  twitter: 'https://twitter.com/sword_and_magic',
  github: '',
  chains: ['eos']
}, {
  name: 'dmail',
  description: 'Welcome to dmail Beta! We are so excited to have you participate as we launch our Beta platform. In the early stages we are covering the simplest of functionality, which is sending and receiving messages. In the very near future, we will be adding a bunch of new features which we know the community is going to ask for.',
  shortDescription: 'dmail is the first decentralized email on the blockchain',
  symbol: 'MAIL',
  statistics: true,
  accounts: ['dmaildotcobp'],
  logo: 'https://www.dmail.co/logosym_256.png',
  website: 'https://dmail.co',
  app: '',
  telegram: 'https://t.me/dmailcommunity',
  medium: 'https://medium.com/@dmail',
  twitter: 'https://twitter.com/dmaildotco',
  github: '',
  chains: ['eos', 'telos']
}, {
  name: 'Murmur',
  description: 'Murmur is a new age decentralized microblogging platform on EOS that is censorship-resistant, spam-proof and rewarding to use.',
  shortDescription: 'Murmur is a new age decentralized microblogging platform on EOS that is censorship-resistant, spam-proof and rewarding to use.',
  symbol: 'MUR',
  partner: true,
  accounts: ['murmurdappco', 'murmurtokens', 'murmurfreeac'],
  app: 'https://play.google.com/store/apps/details?id=com.murmurdapp',
  logo: 'https://bloks.io/img/dapps/murmur.png',
  website: 'http://murmurdapp.com',
  telegram: 'http://t.me/murmurdapp',
  medium: '',
  twitter: 'http://twitter.com/murmurdapp',
  github: '',
  chains: ['eos']
}, {
  name: 'Emanate',
  description: 'Emanate is EOS for the music industry. An automated, realtime music collaboration and monetisation platform.',
  shortDescription: 'Emanate is decentralised technology for the future of music',
  symbol: 'EMT',
  partner: true,
  accounts: ['emanateoneos', 'emanateissue'],
  app: 'https://emanate.live/',
  logo: 'https://bloks.io/img/dapps/emanate.png',
  website: 'https://emanate.live',
  telegram: 'https://t.me/emanateofficial',
  medium: '',
  twitter: 'https://twitter.com/emanateofficial',
  github: '',
  chains: ['eos']
}, {
  name: 'pixEOS',
  description: 'pixEOS is the first tokenized smart economy for gamers, artists and art enthusiasts.',
  shortDescription: 'pixEOS is the first tokenized smart economy for gamers, artists and art enthusiasts.',
  symbol: 'PIXEOS',
  partner: true,
  accounts: ['pixeos1token', 'pixeos1admin', 'pixeos1start'],
  app: 'https://pixeos.io',
  logo: 'https://bloks.io/img/dapps/pixeos.png',
  website: 'https://pixeos.io',
  telegram: 'https://t.me/PIXEOS',
  medium: '',
  twitter: 'https://twitter.com/eos_pix',
  github: '',
  chains: ['eos']
}, {
  name: 'Everipedia',
  description: 'The Everipedia team plans to build a modern, convenient and decentralized new encyclopedia website, and this goal will be realized with the development of blockchain technology. The new version of Everipedia under development will be based on the EOS network, which will have features such as community autonomy, shielding preventation, and contribution incentives compared to the current version of Everipedia. Founded in 2014, the business network encyclopedia Everipedia, whose name derives from the English words Everything and Encyclopedia, is owned by Everipedia.Inc and has not yet adopted blockchain technology. As of December 2017, Everipedia is the largest English encyclopedia with more than six million entries, including all English entries of Wikipedia. Everipedias requirements for attention are more relaxed, so it has more entries than Wikipedia.',
  shortDescription: 'The Everipedia team plans to build a modern, convenient and decentralized new encyclopedia.',
  symbol: 'IQ',
  partner: true,
  statistics: false,
  accounts: ['everipediaiq', 'eparticlectr'],
  logo: 'https://bloks.io/img/dapps/everipedia.jpg',
  website: '',
  app: 'https://everipedia.org',
  telegram: 'https://t.me/everipedia',
  medium: '',
  twitter: '',
  github: '',
  chains: ['eos']
}, {
  name: 'eosDAC',
  description: 'eosDAC is a Community Owned Blockproducer and a DAC enabler, born out of Dan Larimers concept of Decentralized Autonomous Communities or DACs, around which Block.one developed EOS software.  The vision of eosDAC is that EOS.IO block production should be open for everyone to contribute and benefit. To realize this vision, eosDAC is an evolving Decentralised Autonomous Community (DAC) focused on EOS.IO Block Production serving the EOS communities worldwide. In doing this, eosDAC is creating the tools and smart contracts it needs to function. It will share these with the EOS communities to help other DACs thrive on the EOS.IO blockchains.  In order to function as a DAC, eosDAC is creating open source tools and will be sharing them as a DAC Toolkit, that anyone can use, modify to setup and run a DAC.',
  shortDescription: 'eosDAC is creating open source tools and will be sharing them as a DAC Toolkit to enable DACs',
  symbol: 'EOSDAC',
  partner: false,
  statistics: false,
  accounts: ['eosdactokens', 'eosdacserver', 'eosdacthedac', 'daccustodian'],
  logo: 'https://raw.githubusercontent.com/eoscafe/eos-dapps/master/logos/eosdac.png',
  website: '',
  app: 'members.eosdac.io',
  discord: 'https://discord.io/eosdac',
  telegram: 'https://t.me/eosdacio',
  medium: '',
  twitter: '',
  github: 'https://github.com/eosdac',
  chains: ['eos']
}, {
  name: 'DEOS Games',
  description: 'Deos Games are casino games built on EOS blockchain. Play zero edge games with our DEOS token and participate in bankroll staking.',
  shortDescription: 'Deos Games are casino games built on the EOS blockchain. Play zero edge games with DEOS token.',
  symbol: 'DEOS',
  statistics: false,
  accounts: ['thedeosgames', 'deosgameissu'],
  logo: 'https://bloks.io/img/dapps/deosgames.png',
  website: 'https://deosgames.com',
  app: 'https://app.deosgames.com',
  telegram: 'https://t.me/deosgameschat',
  medium: 'https://medium.com/deos-games',
  twitter: '',
  github: '',
  chains: ['eos']
}, {
  name: 'Chintai',
  description: 'Chintai is a community-owned, feeless, 100% on-chain, multisig decentralized token leasing platform where users can lend their EOS on the market to earn interest from other users to borrow who need access to CPU/NET bandwidth.',
  shortDescription: 'Chintai is a community-owned, feeless, 100% on-chain, multisig decentralized token leasing platform.',
  symbol: '',
  statistics: false,
  accounts: ['chintailease', 'chintaiproxy', 'bidchextoken', 'chexchexchex'],
  logo: 'https://bloks.io/img/dapps/chintai.png',
  website: 'http://chintai.io',
  app: 'https://eos.chintai.io/exchange/EOS28D',
  telegram: 'https://t.me/ChintaiEOS',
  medium: 'https://medium.com/@ChintaiEOS',
  twitter: 'https://twitter.com/chintaieos',
  github: 'https://github.com/chintai-platform',
  chains: ['eos']
}, {
  name: 'Newdex',
  description: 'Newdex is the first EOS based decentralized exchange in the world, upholding the characteristics of safe, fast and transparent, devoting to create a new-generation platform for digital assets exchange, leading the industry into an ideal new era.',
  shortDescription: 'Newdex is the first EOS based decentralized exchange in the world.',
  symbol: '',
  accounts: ['newdexpocket'],
  logo: 'https://bloks.io/img/dapps/newdex.png',
  website: 'https://newdex.io',
  app: 'https://newdex.io',
  telegram: '',
  medium: '',
  twitter: 'https://twitter.com/NewdexOfficial',
  github: '',
  chains: ['eos']
}, {
  name: 'EOS Name Swaps',
  description: 'An open-source EOS account exchange that puts the security of its users first.',
  shortDescription: 'An open-source EOS account exchange that puts the security of its users first.',
  symbol: '',
  statistics: false,
  accounts: ['eosnameswaps'],
  logo: 'https://bloks.io/img/dapps/eosnameswaps.png',
  website: 'https://www.eosnameswaps.com/',
  app: 'https://www.eosnameswaps.com/',
  telegram: 'https://t.me/eosnameswaps',
  medium: '',
  twitter: 'https://twitter.com/Starry3017Night',
  github: 'https://github.com/StarryJapanNight/eosnameswaps',
  chains: ['eos']
}];

var exchanges = {
  'Bithumb': {
    'name': 'Bithumb',
    'description': '비트코인, 이더리움, 비트코인캐시, 리플, 라이트코인, 대시, 모네로, 비트코인골드, 이오스, 이더리움클래식, 퀀텀, 제트캐시, 실시간 시세, 쉽고 안전한 거래.',
    'accounts': ['bithumbshiny'],
    'logo': 'https://raw.githubusercontent.com/eoscafe/eos-dapps/master/logos/placeholder.png',
    'website': 'https://www.bithumb.com/'
  },
  'OKEx': {
    'name': 'OKEx',
    'description': 'OKEx is the leading global bitcoin exchange. Secured with bank-level SSL encryption and cold storage.',
    'accounts': ['okexoffiline'],
    'logo': 'https://raw.githubusercontent.com/eoscafe/eos-dapps/master/logos/placeholder.png',
    'website': 'https://www.okex.com/'
  },
  'Bitfinex': {
    'name': 'Bitfinex',
    'description': 'Bitfinex is a full-featured spot trading platform for major digital assets & cryptocurrencies, including Bitcoin, Ethereum, EOS, Litecoin, Ripple, NEO, Monero and many more.',
    'accounts': ['bitfinexcw55', 'bitfinexcw13', 'bitfinexcw11', 'bitfinexcw24', 'bitfinexcw15', 'bitfinexcw32', 'bitfinexcw21', 'bitfinexcw31', 'bitfinexcw25', 'bitfinexcw23', 'bitfinexcw33', 'bitfinexcw22', 'bitfinexcw12', 'bitfinexcw14'],
    'logo': 'https://raw.githubusercontent.com/eoscafe/eos-dapps/master/logos/placeholder.png',
    'website': 'https://bitfinex.com/'
  },
  'Gate.io': {
    'name': 'Gate.io',
    'description': 'Gate.io is a bitcoin exchange platform which supports BTC, LTC, Ethereum, Qtum and more blockchain assets trading.',
    'accounts': ['gateiowallet'],
    'logo': 'https://raw.githubusercontent.com/eoscafe/eos-dapps/master/logos/placeholder.png',
    'website': 'https://www.gate.io/'
  },
  'Kraken': {
    'name': 'Kraken',
    'description': 'Buy, sell and margin trade Bitcoin (BTC) and Etherum (ETH) in exchange with EUR, USD, CAD, GBP, and JPY.',
    'accounts': ['krakenkraken'],
    'logo': 'https://raw.githubusercontent.com/eoscafe/eos-dapps/master/logos/placeholder.png',
    'website': 'https://www.kraken.com/'
  },
  'Newdex': {
    'name': 'Newdex',
    'description': 'The first EOS based decentralized exchange in the world.',
    'accounts': ['newdexpocket'],
    'logo': '/img/exchanges/newdex.png',
    'website': 'https://newdex.io/',
    linkGenerator: function linkGenerator(token, pair) {
      return "https://newdex.io/trade/" + token.account + "-" + pair.pair_base.toLowerCase() + "-" + pair.pair_quote.toLowerCase();
    }
  },
  'DefiBox': {
    'name': 'DefiBox',
    'description': 'One-stop DeFi application platform on EOS..',
    'accounts': ['token.defi', 'swap.defi'],
    'logo': 'https://raw.githubusercontent.com/eoscafe/eos-airdrops/master/logos/token.defi-box.png',
    'website': 'https://defibox.io/',
    linkGenerator: function linkGenerator(_, __) {
      return "https://defibox.io/";
    }
  },
  'Chaince': {
    'name': 'Chaince',
    'description': 'A Superior Blockchain Asset Trading Platform Focusing on EOS Projects',
    'accounts': ['chainceoneos'],
    'logo': '/img/exchanges/chaince.png',
    'website': 'https://chaince.com/',
    linkGenerator: function linkGenerator(_, pair) {
      return "https://chaince.com/trade/" + pair.pair_base.toLowerCase() + pair.pair_quote.toLowerCase();
    }
  },
  'Dexeos': {
    'name': 'Dexeos',
    'description': 'The World\'s First EOS-based Decentralized Exchange',
    'accounts': ['dexeoswallet'],
    'logo': '/img/exchanges/dexeos.svg',
    'website': 'https://dexeos.io/',
    linkGenerator: function linkGenerator(_, pair) {
      return "https://dexeos.io/trade/" + pair.pair_base.toUpperCase();
    }
  },
  'Hoo': {
    'name': 'Hoo',
    'description': 'One-stop blockchain asset service platform',
    'accounts': ['hoo.com'],
    'logo': '/img/exchanges/hoo.jpg',
    'website': 'https://hoo.com/',
    linkGenerator: function linkGenerator(_, pair) {
      return "https://hoo.com/trade/" + pair.pair_base.toLowerCase() + "-" + pair.pair_quote.toLowerCase();
    }
  },
  'Whaleex': {
    'name': 'Whaleex',
    'description': '#1 Decentralized Exchange in the World',
    'accounts': ['whaleextrust'],
    'logo': '/img/exchanges/whaleex.png',
    'website': 'https://www.whaleex.com',
    linkGenerator: function linkGenerator(_, pair) {
      return "https://www.whaleex.com/trade/" + pair.pair_base + "_" + pair.pair_quote;
    }
  },
  'Chainrift': {
    'name': 'Chainrift',
    'description': 'A marketplace for digital currencies',
    'accounts': [],
    'logo': '/img/exchanges/chainrift.png',
    'website': 'https://www.chainrift.com/',
    linkGenerator: function linkGenerator(_, pair) {
      return "https://www.chainrift.com/trading?coinpair=" + pair.pair_base + "/" + pair.pair_quote;
    }
  },
  'Eosdaq': {
    'name': 'EOSDAQ',
    'description': 'A Standard of On-Chain DEX',
    'accounts': [],
    'logo': '/img/exchanges/eosdaq.png',
    'website': 'https://www.eosdaq.com/',
    linkGenerator: function linkGenerator(_, pair) {
      return "https://eosdaq.com/exchange/" + pair.pair_base + "_" + pair.pair_quote;
    }
  },
  'BigONE': {
    'name': 'BigONE',
    'description': 'A Standard of On-Chain DEX',
    'accounts': [],
    'logo': '/img/exchanges/bigONE.jpg',
    'website': 'https://big.one',
    linkGenerator: function linkGenerator(_, pair) {
      return "https://big.one/trade/" + pair.pair_base + "-" + pair.pair_quote;
    }
  },
  'YOLO': {
    'name': 'YOLO',
    'description': 'Instant Token Swaps on EOS',
    'accounts': [],
    'logo': '/img/exchanges/yolo.png',
    'website': 'https://yoloswap.com',
    linkGenerator: function linkGenerator(_, pair) {
      return "https://yoloswap.com/swap/" + pair.pair_quote.toLowerCase() + "-" + pair.pair_base.toLowerCase();
    }
  },
  'Bancor': {
    'name': 'Bancor',
    'description': 'Instant Liquidity.',
    'accounts': [],
    'logo': '/img/exchanges/bancor.png',
    'website': 'https://bancor.network',
    linkGenerator: function linkGenerator(_, pair) {
      return "https://www.bancor.network/token/" + pair.pair_base;
    }
  },
  'Alcor': {
    'name': 'Alcor',
    'description': 'The first self-listing decentralized exchange',
    'accounts': [],
    'logo': '/img/exchanges/alcor.png',
    'website': 'https://alcor.exchange',
    linkGenerator: function linkGenerator(_, __) {
      return "https://www.alcor.exchange/markets";
    }
  },
  'Defis.Network': {
    'name': 'Defis.Network',
    'description': 'An open finance network that integrates a series of DeFi protocols',
    'accounts': [],
    'logo': '/img/exchanges/defis-uncache.png',
    'website': 'https://defis.network',
    linkGenerator: function linkGenerator(_, __) {
      return "https://apps.defis.network/";
    }
  },
  'DolphinSwap': {
    'name': 'DolphinSwap',
    'description': 'DolphinSwap',
    'accounts': [],
    'logo': '/img/exchanges/dolphinswap.png',
    'website': 'https://dolphinswap.io/exchange',
    linkGenerator: function linkGenerator(_, __) {
      return 'https://dolphinswap.io/exchange';
    }
  },
  'Proton': {
    'name': 'ProtonSwap',
    'description': 'ProtonSwap',
    'accounts': [],
    'logo': '/img/exchanges/protonswap.png',
    'website': 'https://protonswap.com',
    linkGenerator: function linkGenerator(_, __) {
      return 'https://protonswap.com';
    }
  },
  'Coingecko': {
    'name': 'CoinGecko',
    'description': 'CoinGecko',
    'accounts': [],
    'logo': '/img/exchanges/coingecko.png',
    'website': 'https://coingecko.com',
    linkGenerator: function linkGenerator(_, __) {
      return 'https://coingecko.com';
    }
  }
};

var SCATTER_DESKTOP = 'ScatterSockets';
var SCATTER_DESKTOP_MANUAL = 'ScatterSocketsManual';
var SCATTER_EXTENSION = 'ScatterExtension';
var LEDGER = 'ledger';
var LEDGER_USB = 'TransportU2F';
var LEDGER_BLE = 'TransportWebBLE';
var LEDGER_WEBUSB = 'TransportWebusb';
var LEDGER_WEBHID = 'TransportWebHID';
var LYNX = 'lynx';
var PROTON = 'proton';
var PROTON_WEB = 'protonweb';
var ANCHOR = 'anchor';
var SIMPLEOS = 'simpleos';
var EOSAUTH = 'eosauth';
var CLEOS = 'cleos';
var EOSC = 'eosc';
var CLIO = 'clio';
var KEYCAT = 'keycat';
var TREZOR = 'trezor';
var SQRL = 'sqrl';
var WOMBAT = 'wombat';
var WAX_CLOUD_WALLET = 'WaxCW';

var historyTypesFeatures = {
  "native": {
    name: 'native',
    actionFilter: false,
    tokenFilter: false,
    dateFilter: false,
    contractActionFilter: false,
    total: 0
  },
  dfuse: {
    name: 'dfuse',
    actionFilter: true,
    tokenFilter: true,
    dateFilter: true,
    contractActionFilter: true,
    total: 4
  },
  hyperion: {
    name: 'hyperion',
    actionFilter: true,
    tokenFilter: true,
    dateFilter: true,
    contractActionFilter: true,
    total: 3
  }
};

var _chainInfo;

var chainInfo = (_chainInfo = {}, _chainInfo['proton-test'] = {
  key: 'proton-test',
  text: 'Proton Testnet',
  value: 'https://testnet.protonscan.io',
  image: '/img/chains/proton.png',
  testnet: true
}, _chainInfo.local = {
  key: 'local',
  text: 'Local Testnet',
  value: 'https://local.bloks.io',
  image: '/img/chains/local.png',
  testnet: true
}, _chainInfo['wax-test'] = {
  key: 'wax-test',
  text: 'WAX Testnet',
  value: 'https://wax-test.bloks.io',
  image: '/img/chains/wax.png',
  testnet: true
}, _chainInfo['fio-test'] = {
  key: 'fio-test',
  text: 'FIO Testnet',
  value: 'https://fio-test.bloks.io',
  image: '/img/chains/fio.png',
  testnet: true
}, _chainInfo.jungle3 = {
  key: 'jungle3',
  text: 'Jungle3 Testnet',
  value: 'https://jungle3.bloks.io',
  image: '/img/chains/jungle.png',
  testnet: true
}, _chainInfo.kylin = {
  key: 'kylin',
  text: 'Kylin Testnet',
  value: 'https://kylin.bloks.io',
  image: '/img/chains/kylin.png',
  testnet: true
}, _chainInfo.proton = {
  key: 'proton',
  text: 'Proton',
  value: 'https://protonscan.io',
  image: '/img/chains/proton.png'
}, _chainInfo.eos = {
  key: 'eos',
  text: 'EOS',
  value: 'https://bloks.io',
  image: '/img/chains/eos.png'
}, _chainInfo.wax = {
  key: 'wax',
  text: 'WAX',
  value: 'https://wax.bloks.io',
  image: '/img/chains/wax.png'
}, _chainInfo.fio = {
  key: 'fio',
  text: 'FIO',
  value: 'https://fio.bloks.io',
  image: '/img/chains/fio.png'
}, _chainInfo);

var getCommonConstants = function getCommonConstants(chain) {
  return {
    MAX_RPC_SYNC_SECONDS_BEHIND: 20,
    IMAGE_PROXY: 'https://www.api.bloks.io/image-proxy',
    WRAP_CONTRACT: 'proton.wrap',
    BLOKS_API: 'https://www.api.bloks.io',
    ESR_PROTOCOL: chain === 'proton' ? 'proton' : 'proton-dev',
    METAL_PROTON_ENDPOINT: chain === 'proton' ? 'https://api.protonchain.com' : 'https://api-dev.protonchain.com',
    SWAP_URL: chain === 'proton' ? 'https://otc.protonswap.com' : 'https://otc-test.protonswap.com',
    WRAP_SERVER_URL: chain === 'proton' ? 'https://www.api.bloks.io/proton-wrap-public2' : 'https://www.api.bloks.io/proton-wrap-testnet-public2'
  };
};

var generateProviderEndpoints = function generateProviderEndpoints(chainId, actionEndpoints) {
  return [{
    chainId: chainId,
    port: 443,
    protocol: 'https',
    host: actionEndpoints[0].substr(8),
    httpEndpoint: actionEndpoints[0],
    blockchain: 'eos'
  }];
};

var DEFAULT_ENDPOINTS = ['https://eos.greymass.com', 'https://eos.eoscafeblock.com', 'https://api.main.alohaeos.com', 'https://api.eossweden.org'];
var ACTIONS_ENDPOINTS = ['https://eos.greymass.com'];
var TRANSACTIONS_ENDPOINTS = ['https://eos.greymass.com', 'https://api.eossweden.org'];
var ALOHA_PROXY_URL = 'https://www.alohaeos.com/vote/proxy';
var API_URL = 'https://www.api.bloks.io';
var ATOMICASSETS_API = 'https://eos.api.atomicassets.io';
var BLOKS_PROXY = 'bloksioproxy';
var CHAIN = 'eos';
var CHAIN_ID = 'aca376f206b8fc25a6ed44dbdc66547c36c6c33e3a119ffbeaef943642f0e906';
var CHAIN_START_DATE = /*#__PURE__*/new Date('2018-06-08');
var CORE_PRECISION = 4;
var CORE_SYMBOL = 'EOS';
var DISPLAY_CHAIN = 'EOS';
var DOMAIN_TITLE = 'EOS Bloks.io';
var HISTORY_TYPES = ['native', 'hyperion'];
var HYPERION_URL = 'https://eos.hyperion.eosrio.io';
var KEY_PREFIX = 'EOS';
var LIGHT_API = 'https://api.light.xeos.me';
var NFTS_ENABLED = true;
var PROVIDER_ENDPOINTS = /*#__PURE__*/generateProviderEndpoints(CHAIN_ID, ACTIONS_ENDPOINTS);
var REX_ENABLED = true;
var SIMPLEASSETS_API = 'https://eos.api.simpleassets.io';
var SUPPORTS_FREE_CPU = true;
var SUPPORTS_RENTBW = true;
var VOTING_ENABLED = true;
var constants = {
  ACTIONS_ENDPOINTS: ACTIONS_ENDPOINTS,
  ALOHA_PROXY_URL: ALOHA_PROXY_URL,
  API_URL: API_URL,
  ATOMICASSETS_API: ATOMICASSETS_API,
  BLOKS_PROXY: BLOKS_PROXY,
  CHAIN: CHAIN,
  CHAIN_ID: CHAIN_ID,
  CHAIN_START_DATE: CHAIN_START_DATE,
  CORE_PRECISION: CORE_PRECISION,
  CORE_SYMBOL: CORE_SYMBOL,
  DEFAULT_ENDPOINTS: DEFAULT_ENDPOINTS,
  DISPLAY_CHAIN: DISPLAY_CHAIN,
  DOMAIN_TITLE: DOMAIN_TITLE,
  HISTORY_TYPES: HISTORY_TYPES,
  HYPERION_URL: HYPERION_URL,
  KEY_PREFIX: KEY_PREFIX,
  LIGHT_API: LIGHT_API,
  NFTS_ENABLED: NFTS_ENABLED,
  PROVIDER_ENDPOINTS: PROVIDER_ENDPOINTS,
  REX_ENABLED: REX_ENABLED,
  SIMPLEASSETS_API: SIMPLEASSETS_API,
  SUPPORTS_FREE_CPU: SUPPORTS_FREE_CPU,
  SUPPORTS_RENTBW: SUPPORTS_RENTBW,
  TRANSACTIONS_ENDPOINTS: TRANSACTIONS_ENDPOINTS,
  VOTING_ENABLED: VOTING_ENABLED
};

var DEFAULT_ENDPOINTS$1 = ['https://wax.greymass.com', 'https://wax.eoscafeblock.com', 'https://api.waxsweden.org', 'https://chain.wax.io', 'https://wax.eosrio.io'];
var ACTIONS_ENDPOINTS$1 = ['https://wax.greymass.com', 'https://api.waxsweden.org', 'https://wax.eosrio.io', 'https://chain.wax.io'];
var TRANSACTIONS_ENDPOINTS$1 = ['https://wax.greymass.com', 'https://api.waxsweden.org', 'https://wax.eosrio.io', 'https://chain.wax.io'];
var ALOHA_PROXY_URL$1 = 'https://www.alohaeos.com/vote/proxy/waxmain';
var API_URL$1 = 'https://www.api.bloks.io/wax';
var ATOMICASSETS_API$1 = 'https://wax.api.atomicassets.io';
var BLOKS_PROXY$1 = 'bloksioproxy';
var CHAIN$1 = 'wax';
var CHAIN_ID$1 = '1064487b3cd1a897ce03ae5b6a865651747e2e152090f99c1d19d44e01aea5a4';
var CHAIN_START_DATE$1 = /*#__PURE__*/new Date('2019-06-24');
var CORE_PRECISION$1 = 8;
var CORE_SYMBOL$1 = 'WAX';
var DISPLAY_CHAIN$1 = 'WAX';
var DOMAIN_TITLE$1 = 'WAX | Bloks.io';
var HISTORY_TYPES$1 = ['native', 'hyperion'];
var HYPERION_URL$1 = 'https://wax.eosrio.io';
var KEY_PREFIX$1 = 'EOS';
var LIGHT_API$1 = 'https://lightapi.eosamsterdam.net';
var NFTS_ENABLED$1 = true;
var PROVIDER_ENDPOINTS$1 = /*#__PURE__*/generateProviderEndpoints(CHAIN_ID$1, ACTIONS_ENDPOINTS$1);
var SIMPLEASSETS_API$1 = 'https://wax.api.simpleassets.io';
var VOTING_ENABLED$1 = true;
var constants$1 = {
  ACTIONS_ENDPOINTS: ACTIONS_ENDPOINTS$1,
  ALOHA_PROXY_URL: ALOHA_PROXY_URL$1,
  API_URL: API_URL$1,
  ATOMICASSETS_API: ATOMICASSETS_API$1,
  BLOKS_PROXY: BLOKS_PROXY$1,
  CHAIN: CHAIN$1,
  CHAIN_ID: CHAIN_ID$1,
  CHAIN_START_DATE: CHAIN_START_DATE$1,
  CORE_PRECISION: CORE_PRECISION$1,
  CORE_SYMBOL: CORE_SYMBOL$1,
  DEFAULT_ENDPOINTS: DEFAULT_ENDPOINTS$1,
  DISPLAY_CHAIN: DISPLAY_CHAIN$1,
  DOMAIN_TITLE: DOMAIN_TITLE$1,
  HISTORY_TYPES: HISTORY_TYPES$1,
  HYPERION_URL: HYPERION_URL$1,
  KEY_PREFIX: KEY_PREFIX$1,
  LIGHT_API: LIGHT_API$1,
  NFTS_ENABLED: NFTS_ENABLED$1,
  PROVIDER_ENDPOINTS: PROVIDER_ENDPOINTS$1,
  SIMPLEASSETS_API: SIMPLEASSETS_API$1,
  TRANSACTIONS_ENDPOINTS: TRANSACTIONS_ENDPOINTS$1,
  VOTING_ENABLED: VOTING_ENABLED$1
};

var DEFAULT_ENDPOINTS$2 = ['https://proton.greymass.com', 'https://proton.cryptolions.io', 'https://proton.eosusa.news', "https://frankfurt.protondata.net"];
var TRANSACTIONS_ENDPOINTS$2 = ['https://proton.greymass.com', 'https://proton.cryptolions.io'];
var ACTIONS_ENDPOINTS$2 = ['https://proton.greymass.com'];
var API_URL$2 = 'https://www.api.bloks.io/proton';
var ATOMICASSETS_API$2 = 'https://proton.api.atomicassets.io';
var CHAIN$2 = 'proton';
var CHAIN_ID$2 = '384da888112027f0321850a169f737c33e53b388aad48b5adace4bab97f437e0';
var CHAIN_START_DATE$2 = /*#__PURE__*/new Date('Apr 22, 2020');
var CORE_PRECISION$2 = 4;
var CORE_SYMBOL$2 = 'XPR';
var DISPLAY_CHAIN$2 = 'Proton';
var DOMAIN_TITLE$2 = 'ProtonScan';
var HISTORY_TYPES$2 = ['native', 'hyperion'];
var HYPERION_URL$2 = 'http://proton.pink.gg';
var KEY_PREFIX$2 = 'EOS';
var LIGHT_API$2 = 'https://lightapi.eosamsterdam.net';
var MAX_VOTES = 4;
var NFTS_ENABLED$2 = true;
var PROVIDER_ENDPOINTS$2 = /*#__PURE__*/generateProviderEndpoints(CHAIN_ID$2, ACTIONS_ENDPOINTS$2);
var VOTING_ENABLED$2 = true;
var constants$2 = {
  ACTIONS_ENDPOINTS: ACTIONS_ENDPOINTS$2,
  API_URL: API_URL$2,
  ATOMICASSETS_API: ATOMICASSETS_API$2,
  CHAIN: CHAIN$2,
  CHAIN_ID: CHAIN_ID$2,
  CHAIN_START_DATE: CHAIN_START_DATE$2,
  CORE_PRECISION: CORE_PRECISION$2,
  CORE_SYMBOL: CORE_SYMBOL$2,
  DEFAULT_ENDPOINTS: DEFAULT_ENDPOINTS$2,
  DISPLAY_CHAIN: DISPLAY_CHAIN$2,
  DOMAIN_TITLE: DOMAIN_TITLE$2,
  HISTORY_TYPES: HISTORY_TYPES$2,
  HYPERION_URL: HYPERION_URL$2,
  KEY_PREFIX: KEY_PREFIX$2,
  LIGHT_API: LIGHT_API$2,
  MAX_VOTES: MAX_VOTES,
  NFTS_ENABLED: NFTS_ENABLED$2,
  PROVIDER_ENDPOINTS: PROVIDER_ENDPOINTS$2,
  TRANSACTIONS_ENDPOINTS: TRANSACTIONS_ENDPOINTS$2,
  VOTING_ENABLED: VOTING_ENABLED$2
};

var DEFAULT_ENDPOINTS$3 = ['https://fio.greymass.com', 'https://fio.eossweden.org', 'https://fio.eosusa.news'];
var TRANSACTIONS_ENDPOINTS$3 = ['https://fio.greymass.com', 'https://fio.eossweden.org', 'https://fio.eosusa.news'];
var ACTIONS_ENDPOINTS$3 = ['https://fio.greymass.com', 'https://fio.eossweden.org', 'https://fio.eosusa.news'];
var ALOHA_PROXY_URL$2 = 'https://www.alohaeos.com/vote/proxy/fiomain';
var API_URL$3 = 'https://www.api.bloks.io/fio';
var CHAIN$3 = 'fio';
var CHAIN_ID$3 = '21dcae42c0182200e93f954a074011f9048a7624c6fe81d3c9541a614a88bd1c';
var CHAIN_START_DATE$3 = /*#__PURE__*/new Date('Mar 24, 2020');
var CORE_PRECISION$3 = 9;
var CORE_SYMBOL$3 = 'FIO';
var DISABLE_MEMO = true;
var DISPLAY_CHAIN$3 = 'FIO';
var DOMAIN_TITLE$3 = 'FIO Bloks.io';
var FIO_FEES_ACCOUNT = 'fees@bloks';
var HISTORY_TYPES$3 = ['native', 'hyperion'];
var HYPERION_URL$3 = 'https://fio.eossweden.org';
var KEY_PREFIX$3 = 'FIO';
var PROVIDER_ENDPOINTS$3 = /*#__PURE__*/generateProviderEndpoints(CHAIN_ID$3, ACTIONS_ENDPOINTS$3);
var VOTING_ENABLED$3 = true;
var constants$3 = {
  ACTIONS_ENDPOINTS: ACTIONS_ENDPOINTS$3,
  ALOHA_PROXY_URL: ALOHA_PROXY_URL$2,
  API_URL: API_URL$3,
  CHAIN: CHAIN$3,
  CHAIN_ID: CHAIN_ID$3,
  CHAIN_START_DATE: CHAIN_START_DATE$3,
  CORE_PRECISION: CORE_PRECISION$3,
  CORE_SYMBOL: CORE_SYMBOL$3,
  DEFAULT_ENDPOINTS: DEFAULT_ENDPOINTS$3,
  DISABLE_MEMO: DISABLE_MEMO,
  DISPLAY_CHAIN: DISPLAY_CHAIN$3,
  DOMAIN_TITLE: DOMAIN_TITLE$3,
  FIO_FEES_ACCOUNT: FIO_FEES_ACCOUNT,
  HISTORY_TYPES: HISTORY_TYPES$3,
  HYPERION_URL: HYPERION_URL$3,
  KEY_PREFIX: KEY_PREFIX$3,
  PROVIDER_ENDPOINTS: PROVIDER_ENDPOINTS$3,
  TRANSACTIONS_ENDPOINTS: TRANSACTIONS_ENDPOINTS$3,
  VOTING_ENABLED: VOTING_ENABLED$3
};

var DEFAULT_ENDPOINTS$4 = [];
var ACTIONS_ENDPOINTS$4 = [];
var TRANSACTIONS_ENDPOINTS$4 = [];
var API_URL$4 = '';
var CHAIN$4 = 'local';
var CHAIN_ID$4 = '';
var CHAIN_START_DATE$4 = undefined;
var CORE_PRECISION$4 = 4;
var CORE_SYMBOL$4 = 'EOS';
var DISPLAY_CHAIN$4 = 'Local';
var DOMAIN_TITLE$4 = 'Local Bloks.io';
var HISTORY_TYPES$4 = ['native'];
var KEY_PREFIX$4 = 'EOS';
var PROVIDER_ENDPOINTS$4 = [];
var VOTING_ENABLED$4 = true;
var constants$4 = {
  ACTIONS_ENDPOINTS: ACTIONS_ENDPOINTS$4,
  API_URL: API_URL$4,
  CHAIN: CHAIN$4,
  CHAIN_ID: CHAIN_ID$4,
  CHAIN_START_DATE: CHAIN_START_DATE$4,
  CORE_PRECISION: CORE_PRECISION$4,
  CORE_SYMBOL: CORE_SYMBOL$4,
  DEFAULT_ENDPOINTS: DEFAULT_ENDPOINTS$4,
  DISPLAY_CHAIN: DISPLAY_CHAIN$4,
  DOMAIN_TITLE: DOMAIN_TITLE$4,
  HISTORY_TYPES: HISTORY_TYPES$4,
  KEY_PREFIX: KEY_PREFIX$4,
  PROVIDER_ENDPOINTS: PROVIDER_ENDPOINTS$4,
  TRANSACTIONS_ENDPOINTS: TRANSACTIONS_ENDPOINTS$4,
  VOTING_ENABLED: VOTING_ENABLED$4
};

var DEFAULT_ENDPOINTS$5 = [// 'https://jungleapi.eossweden.org',
'https://api.jungle.alohaeos.com', 'https://jungle2.cryptolions.io', 'https://jungle.eosphere.io', 'https://eos-jungle.eosblocksmith.io'];
var ACTIONS_ENDPOINTS$5 = ['https://jungle.eossweden.org'];
var TRANSACTIONS_ENDPOINTS$5 = ['https://jungle.eossweden.org'];
var API_URL$5 = 'https://www.api.bloks.io/jungle';
var BLOKS_PROXY$2 = 'blokspartner';
var CHAIN$5 = 'jungle';
var CHAIN_ID$5 = 'e70aaab8997e1dfce58fbfac80cbbb8fecec7b99cf982a9444273cbc64c41473';
var CHAIN_START_DATE$5 = /*#__PURE__*/new Date('Nov 23, 2018');
var CORE_PRECISION$5 = 4;
var CORE_SYMBOL$5 = 'EOS';
var DISPLAY_CHAIN$5 = 'Jungle';
var DOMAIN_TITLE$5 = 'Jungle Bloks.io';
var HISTORY_TYPES$5 = ['hyperion', 'native'];
var HYPERION_URL$4 = 'https://jungle2.cryptolions.io';
var KEY_PREFIX$5 = 'EOS';
var LIGHT_API$3 = 'https://lightapi.eosgeneva.io';
var NFTS_ENABLED$3 = true;
var PROVIDER_ENDPOINTS$5 = /*#__PURE__*/generateProviderEndpoints(CHAIN_ID$5, ACTIONS_ENDPOINTS$5);
var REX_ENABLED$1 = true;
var VOTING_ENABLED$5 = true;
var constants$5 = {
  ACTIONS_ENDPOINTS: ACTIONS_ENDPOINTS$5,
  API_URL: API_URL$5,
  BLOKS_PROXY: BLOKS_PROXY$2,
  CHAIN: CHAIN$5,
  CHAIN_ID: CHAIN_ID$5,
  CHAIN_START_DATE: CHAIN_START_DATE$5,
  CORE_PRECISION: CORE_PRECISION$5,
  CORE_SYMBOL: CORE_SYMBOL$5,
  DEFAULT_ENDPOINTS: DEFAULT_ENDPOINTS$5,
  DISPLAY_CHAIN: DISPLAY_CHAIN$5,
  DOMAIN_TITLE: DOMAIN_TITLE$5,
  HISTORY_TYPES: HISTORY_TYPES$5,
  HYPERION_URL: HYPERION_URL$4,
  KEY_PREFIX: KEY_PREFIX$5,
  LIGHT_API: LIGHT_API$3,
  NFTS_ENABLED: NFTS_ENABLED$3,
  PROVIDER_ENDPOINTS: PROVIDER_ENDPOINTS$5,
  REX_ENABLED: REX_ENABLED$1,
  TRANSACTIONS_ENDPOINTS: TRANSACTIONS_ENDPOINTS$5,
  VOTING_ENABLED: VOTING_ENABLED$5
};

var DEFAULT_ENDPOINTS$6 = ['https://jungle3.cryptolions.io', 'https://api.jungle3.alohaeos.com', 'https://jungle3.eosusa.news'];
var ACTIONS_ENDPOINTS$6 = ['https://jungle3.cryptolions.io', 'https://jungle3.eosusa.news'];
var TRANSACTIONS_ENDPOINTS$6 = ['https://jungle3.cryptolions.io', 'https://jungle3.eosusa.news'];
var API_URL$6 = 'https://www.api.bloks.io/jungle3';
var CHAIN$6 = 'jungle3';
var CHAIN_ID$6 = '2a02a0053e5a8cf73a56ba0fda11e4d92e0238a4a2aa74fccf46d5a910746840';
var CHAIN_START_DATE$6 = /*#__PURE__*/new Date('Feb 19, 2020');
var CORE_PRECISION$6 = 4;
var CORE_SYMBOL$6 = 'EOS';
var DISPLAY_CHAIN$6 = 'Jungle 3';
var DOMAIN_TITLE$6 = 'Jungle 3 Bloks.io';
var HISTORY_TYPES$6 = ['hyperion'];
var HYPERION_URL$5 = 'https://jungle3.cryptolions.io';
var KEY_PREFIX$6 = 'EOS';
var PROVIDER_ENDPOINTS$6 = /*#__PURE__*/generateProviderEndpoints(CHAIN_ID$6, ACTIONS_ENDPOINTS$6);
var REX_ENABLED$2 = true;
var SUPPORTS_RENTBW$1 = true;
var VOTING_ENABLED$6 = true;
var constants$6 = {
  ACTIONS_ENDPOINTS: ACTIONS_ENDPOINTS$6,
  API_URL: API_URL$6,
  CHAIN: CHAIN$6,
  CHAIN_ID: CHAIN_ID$6,
  CHAIN_START_DATE: CHAIN_START_DATE$6,
  CORE_PRECISION: CORE_PRECISION$6,
  CORE_SYMBOL: CORE_SYMBOL$6,
  DEFAULT_ENDPOINTS: DEFAULT_ENDPOINTS$6,
  DISPLAY_CHAIN: DISPLAY_CHAIN$6,
  DOMAIN_TITLE: DOMAIN_TITLE$6,
  HISTORY_TYPES: HISTORY_TYPES$6,
  HYPERION_URL: HYPERION_URL$5,
  KEY_PREFIX: KEY_PREFIX$6,
  PROVIDER_ENDPOINTS: PROVIDER_ENDPOINTS$6,
  REX_ENABLED: REX_ENABLED$2,
  SUPPORTS_RENTBW: SUPPORTS_RENTBW$1,
  TRANSACTIONS_ENDPOINTS: TRANSACTIONS_ENDPOINTS$6,
  VOTING_ENABLED: VOTING_ENABLED$6
};

var DEFAULT_ENDPOINTS$7 = ['https://kylin.eosn.io'];
var ACTIONS_ENDPOINTS$7 = ['https://kylin.eosn.io'];
var TRANSACTIONS_ENDPOINTS$7 = ['https://kylin.eosn.io'];
var API_URL$7 = 'https://www.api.bloks.io/kylin';
var BLOKS_PROXY$3 = 'blokspartner';
var CHAIN$7 = 'kylin';
var CHAIN_ID$7 = '5fff1dae8dc8e2fc4d5b23b2c7665c97f9e9d8edf2b6485a86ba311c25639191';
var CHAIN_START_DATE$7 = /*#__PURE__*/new Date('Jul 10, 2018');
var CORE_PRECISION$7 = 4;
var CORE_SYMBOL$7 = 'EOS';
var DISPLAY_CHAIN$7 = 'Kylin';
var DOMAIN_TITLE$7 = 'Kylin Bloks.io';
var HISTORY_TYPES$7 = ['hyperion', 'native'];
var HYPERION_URL$6 = 'https://kylin.eosusa.news';
var KEY_PREFIX$7 = 'EOS';
var PROVIDER_ENDPOINTS$7 = /*#__PURE__*/generateProviderEndpoints(CHAIN_ID$7, ACTIONS_ENDPOINTS$7);
var VOTING_ENABLED$7 = true;
var constants$7 = {
  ACTIONS_ENDPOINTS: ACTIONS_ENDPOINTS$7,
  API_URL: API_URL$7,
  BLOKS_PROXY: BLOKS_PROXY$3,
  CHAIN: CHAIN$7,
  CHAIN_ID: CHAIN_ID$7,
  CHAIN_START_DATE: CHAIN_START_DATE$7,
  CORE_PRECISION: CORE_PRECISION$7,
  CORE_SYMBOL: CORE_SYMBOL$7,
  DEFAULT_ENDPOINTS: DEFAULT_ENDPOINTS$7,
  DISPLAY_CHAIN: DISPLAY_CHAIN$7,
  DOMAIN_TITLE: DOMAIN_TITLE$7,
  HISTORY_TYPES: HISTORY_TYPES$7,
  HYPERION_URL: HYPERION_URL$6,
  KEY_PREFIX: KEY_PREFIX$7,
  PROVIDER_ENDPOINTS: PROVIDER_ENDPOINTS$7,
  TRANSACTIONS_ENDPOINTS: TRANSACTIONS_ENDPOINTS$7,
  VOTING_ENABLED: VOTING_ENABLED$7
};

var DEFAULT_ENDPOINTS$8 = ['https://www.api.bloks.io/eos-test-node'];
var ACTIONS_ENDPOINTS$8 = ['https://www.api.bloks.io/eos-test-node'];
var TRANSACTIONS_ENDPOINTS$8 = ['https://www.api.bloks.io/eos-test-node'];
var API_URL$8 = 'https://www.api.bloks.io/eos-test';
var CHAIN$8 = 'eos-test';
var CHAIN_ID$8 = '0db13ab9b321c37c0ba8481cb4681c2788b622c3abfd1f12f0e5353d44ba6e72';
var CHAIN_START_DATE$8 = /*#__PURE__*/new Date('2020-01-14');
var CORE_PRECISION$8 = 4;
var CORE_SYMBOL$8 = 'TNT';
var DISPLAY_CHAIN$8 = 'EOSIO Test';
var DOMAIN_TITLE$8 = 'Bloks.io';
var HISTORY_TYPES$8 = ['native'];
var KEY_PREFIX$8 = 'EOS';
var PROVIDER_ENDPOINTS$8 = /*#__PURE__*/generateProviderEndpoints(CHAIN_ID$8, ACTIONS_ENDPOINTS$8);
var constants$8 = {
  DEFAULT_ENDPOINTS: DEFAULT_ENDPOINTS$8,
  ACTIONS_ENDPOINTS: ACTIONS_ENDPOINTS$8,
  TRANSACTIONS_ENDPOINTS: TRANSACTIONS_ENDPOINTS$8,
  API_URL: API_URL$8,
  PROVIDER_ENDPOINTS: PROVIDER_ENDPOINTS$8,
  CORE_SYMBOL: CORE_SYMBOL$8,
  CHAIN: CHAIN$8,
  DISPLAY_CHAIN: DISPLAY_CHAIN$8,
  HISTORY_TYPES: HISTORY_TYPES$8,
  CHAIN_ID: CHAIN_ID$8,
  DOMAIN_TITLE: DOMAIN_TITLE$8,
  CHAIN_START_DATE: CHAIN_START_DATE$8,
  KEY_PREFIX: KEY_PREFIX$8,
  CORE_PRECISION: CORE_PRECISION$8
};

var DEFAULT_ENDPOINTS$9 = ['https://protontestnet.greymass.com', 'https://proton-testnet.eoscafeblock.com', 'https://testnet.protonchain.com', 'https://test.proton.eosusa.news'];
var TRANSACTIONS_ENDPOINTS$9 = ['https://protontestnet.greymass.com', 'https://testnet.protonchain.com', 'https://test.proton.eosusa.news'];
var ACTIONS_ENDPOINTS$9 = ['https://protontestnet.greymass.com', 'https://testnet.protonchain.com', 'https://test.proton.eosusa.news'];
var API_URL$9 = 'https://www.api.bloks.io/proton-test';
var ATOMICASSETS_API$3 = 'https://test.proton.api.atomicassets.io';
var CHAIN$9 = 'proton-test';
var CHAIN_ID$9 = '71ee83bcf52142d61019d95f9cc5427ba6a0d7ff8accd9e2088ae2abeaf3d3dd';
var CHAIN_START_DATE$9 = /*#__PURE__*/new Date('April 3, 2020');
var CORE_PRECISION$9 = 4;
var CORE_SYMBOL$9 = 'XPR';
var DISPLAY_CHAIN$9 = 'Proton-T';
var DOMAIN_TITLE$9 = 'Proton Testnet';
var HISTORY_TYPES$9 = ['hyperion', 'native'];
var HYPERION_URL$7 = 'https://testnet.proton.pink.gg';
var KEY_PREFIX$9 = 'EOS';
var MAX_VOTES$1 = 4;
var PROVIDER_ENDPOINTS$9 = /*#__PURE__*/generateProviderEndpoints(CHAIN_ID$9, ACTIONS_ENDPOINTS$9);
var VOTING_ENABLED$8 = true;
var constants$9 = {
  ACTIONS_ENDPOINTS: ACTIONS_ENDPOINTS$9,
  API_URL: API_URL$9,
  ATOMICASSETS_API: ATOMICASSETS_API$3,
  CHAIN: CHAIN$9,
  CHAIN_ID: CHAIN_ID$9,
  CHAIN_START_DATE: CHAIN_START_DATE$9,
  CORE_PRECISION: CORE_PRECISION$9,
  CORE_SYMBOL: CORE_SYMBOL$9,
  DEFAULT_ENDPOINTS: DEFAULT_ENDPOINTS$9,
  DISPLAY_CHAIN: DISPLAY_CHAIN$9,
  DOMAIN_TITLE: DOMAIN_TITLE$9,
  HISTORY_TYPES: HISTORY_TYPES$9,
  HYPERION_URL: HYPERION_URL$7,
  KEY_PREFIX: KEY_PREFIX$9,
  MAX_VOTES: MAX_VOTES$1,
  PROVIDER_ENDPOINTS: PROVIDER_ENDPOINTS$9,
  TRANSACTIONS_ENDPOINTS: TRANSACTIONS_ENDPOINTS$9,
  VOTING_ENABLED: VOTING_ENABLED$8
};

var DEFAULT_ENDPOINTS$a = ['https://testnet.wax.eosdetroit.io', 'https://testnet.wax.pink.gg', 'https://testnet.waxsweden.org'];
var TRANSACTIONS_ENDPOINTS$a = ['https://testnet.wax.eosdetroit.io', 'https://testnet.wax.pink.gg', 'https://testnet.waxsweden.org'];
var ACTIONS_ENDPOINTS$a = ['https://testnet.wax.eosdetroit.io', 'https://testnet.wax.pink.gg', 'https://testnet.waxsweden.org'];
var API_URL$a = 'https://www.api.bloks.io/wax-test';
var ATOMICASSETS_API$4 = 'https://test.wax.api.atomicassets.io';
var CHAIN$a = 'wax-test';
var CHAIN_ID$a = 'f16b1833c747c43682f4386fca9cbb327929334a762755ebec17f6f23c9b8a12';
var CHAIN_START_DATE$a = /*#__PURE__*/new Date('Dec 5, 2019');
var CORE_PRECISION$a = 8;
var CORE_SYMBOL$a = 'WAX';
var DISPLAY_CHAIN$a = 'WAX-T';
var DOMAIN_TITLE$a = 'WAX Testnet Bloks.io';
var HISTORY_TYPES$a = ['native', 'hyperion'];
var HYPERION_URL$8 = 'https://testnet.waxsweden.org';
var KEY_PREFIX$a = 'EOS';
var LIGHT_API$4 = 'https://testnet-lightapi.eosams.xeos.me';
var PROVIDER_ENDPOINTS$a = /*#__PURE__*/generateProviderEndpoints(CHAIN_ID$a, ACTIONS_ENDPOINTS$a);
var constants$a = {
  ACTIONS_ENDPOINTS: ACTIONS_ENDPOINTS$a,
  API_URL: API_URL$a,
  ATOMICASSETS_API: ATOMICASSETS_API$4,
  CHAIN: CHAIN$a,
  CHAIN_ID: CHAIN_ID$a,
  CHAIN_START_DATE: CHAIN_START_DATE$a,
  CORE_PRECISION: CORE_PRECISION$a,
  CORE_SYMBOL: CORE_SYMBOL$a,
  DEFAULT_ENDPOINTS: DEFAULT_ENDPOINTS$a,
  DISPLAY_CHAIN: DISPLAY_CHAIN$a,
  DOMAIN_TITLE: DOMAIN_TITLE$a,
  HISTORY_TYPES: HISTORY_TYPES$a,
  HYPERION_URL: HYPERION_URL$8,
  KEY_PREFIX: KEY_PREFIX$a,
  LIGHT_API: LIGHT_API$4,
  PROVIDER_ENDPOINTS: PROVIDER_ENDPOINTS$a,
  TRANSACTIONS_ENDPOINTS: TRANSACTIONS_ENDPOINTS$a
};

var DEFAULT_ENDPOINTS$b = ['https://fiotestnet.greymass.com', 'https://test.fio.eosusa.news'];
var TRANSACTIONS_ENDPOINTS$b = ['https://fiotestnet.greymass.com', 'https://test.fio.eosusa.news'];
var ACTIONS_ENDPOINTS$b = ['https://fiotestnet.greymass.com', 'https://test.fio.eosusa.news'];
var API_URL$b = 'https://www.api.bloks.io/fio-test';
var CHAIN$b = 'fio-test';
var CHAIN_ID$b = 'b20901380af44ef59c5918439a1f9a41d83669020319a80574b804a5f95cbd7e';
var CHAIN_START_DATE$b = /*#__PURE__*/new Date('Mar 10, 2020');
var CORE_PRECISION$b = 9;
var CORE_SYMBOL$b = 'FIO';
var DISABLE_MEMO$1 = true;
var DISPLAY_CHAIN$b = 'FIO Test';
var DOMAIN_TITLE$b = 'FIO Test Bloks.io';
var HISTORY_TYPES$b = ['native', 'hyperion'];
var HYPERION_URL$9 = 'https://test.fio.eosusa.news';
var KEY_PREFIX$b = 'FIO';
var PROVIDER_ENDPOINTS$b = /*#__PURE__*/generateProviderEndpoints(CHAIN_ID$b, ACTIONS_ENDPOINTS$b);
var VOTING_ENABLED$9 = true;
var constants$b = {
  ACTIONS_ENDPOINTS: ACTIONS_ENDPOINTS$b,
  API_URL: API_URL$b,
  CHAIN: CHAIN$b,
  CHAIN_ID: CHAIN_ID$b,
  CHAIN_START_DATE: CHAIN_START_DATE$b,
  CORE_PRECISION: CORE_PRECISION$b,
  CORE_SYMBOL: CORE_SYMBOL$b,
  DEFAULT_ENDPOINTS: DEFAULT_ENDPOINTS$b,
  DISABLE_MEMO: DISABLE_MEMO$1,
  DISPLAY_CHAIN: DISPLAY_CHAIN$b,
  DOMAIN_TITLE: DOMAIN_TITLE$b,
  HISTORY_TYPES: HISTORY_TYPES$b,
  HYPERION_URL: HYPERION_URL$9,
  KEY_PREFIX: KEY_PREFIX$b,
  PROVIDER_ENDPOINTS: PROVIDER_ENDPOINTS$b,
  TRANSACTIONS_ENDPOINTS: TRANSACTIONS_ENDPOINTS$b,
  VOTING_ENABLED: VOTING_ENABLED$9
};

var _chainToNetworkConsta;

var chainToNetworkConstantsMap = (_chainToNetworkConsta = {
  eos: constants,
  wax: constants$1,
  proton: constants$2,
  local: constants$4,
  jungle: constants$5,
  jungle3: constants$6,
  kylin: constants$7,
  fio: constants$3
}, _chainToNetworkConsta['eos-test'] = constants$8, _chainToNetworkConsta['proton-test'] = constants$9, _chainToNetworkConsta['wax-test'] = constants$a, _chainToNetworkConsta['fio-test'] = constants$b, _chainToNetworkConsta);
var Constants = /*#__PURE__*/function () {
  function Constants() {
    if (!!Constants.instance) {
      return Constants.instance;
    }
  }

  var _proto = Constants.prototype;

  _proto.initialize = function initialize(chain) {
    if (!chain || !chainToNetworkConstantsMap[chain]) {
      chain = DEFAULT_CHAIN;
    }

    this.setNetwork(chain);
    this.setCommon(chain);
  };

  _proto.setNetwork = function setNetwork(chain) {
    // const networkConstants = await import(`'./networks/${chain}`)
    var networkConstants = chainToNetworkConstantsMap[chain];
    this.setConstants(networkConstants);
    this.setContract(chain, networkConstants.SYSTEM_DOMAIN);
  };

  _proto.setCommon = function setCommon(chain) {
    var commonConstants = getCommonConstants(chain);
    this.setConstants(commonConstants);
  };

  _proto.setContract = function setContract(chain, systemDomain) {
    if (systemDomain === void 0) {
      systemDomain = DEFAULT_SYSTEM_DOMAIN;
    }

    var contractConstants = getContractConstants(chain, systemDomain);
    this.setConstants(contractConstants);
  };

  _proto.setConstants = function setConstants(newConstants) {
    for (var _i = 0, _Object$entries = Object.entries(newConstants); _i < _Object$entries.length; _i++) {
      var _Object$entries$_i = _Object$entries[_i],
          key = _Object$entries$_i[0],
          value = _Object$entries$_i[1];
      this[key] = value;
    }
  };

  return Constants;
}();
var constants$c = /*#__PURE__*/new Constants();

export { ANCHOR, CLEOS, CLIO, Constants, DEFAULT_CHAIN, DEFAULT_SYMBOL, DEFAULT_SYSTEM_DOMAIN, EOSAUTH, EOSC, KEYCAT, LEDGER, LEDGER_BLE, LEDGER_USB, LEDGER_WEBHID, LEDGER_WEBUSB, LYNX, PROTON, PROTON_WEB, SCATTER_DESKTOP, SCATTER_DESKTOP_MANUAL, SCATTER_EXTENSION, SIMPLEOS, SQRL, TREZOR, WAX_CLOUD_WALLET, WOMBAT, chainInfo, chainToNetworkConstantsMap, constants$c as constants, dapps, exchanges, getContractConstants, historyTypesFeatures };
//# sourceMappingURL=constants.esm.js.map
