/*-
 *   BSD LICENSE
 *
 *   Copyright(c) 2010-2014 Intel Corporation. All rights reserved.
 *   All rights reserved.
 *
 *   Redistribution and use in source and binary forms, with or without
 *   modification, are permitted provided that the following conditions
 *   are met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in
 *       the documentation and/or other materials provided with the
 *       distribution.
 *     * Neither the name of Intel Corporation nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 *   THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *   "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *   LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *   A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *   OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *   SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *   LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *   DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *   THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *   OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
//##############################// encoder main file [03sep2018] Encoder is Equiped with HashTable
//##############################// encoder main file [23Apr2018 1200] -- orignal file--used as encoder--twin1
//#include "/home/waqas/Downloads/libRaptorQ-0.1.7/src/cRaptorQ.h"
#include "/home/ahmed/libRaptorQ-0.1.7/src/cRaptorQ.h"
#include <rte_pdump.h>
#include <rte_igmp.h>
#include <rte_timer.h>
#include <signal.h>
#include <pcap.h>
#include <getopt.h>
#include <arpa/inet.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <libgen.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
//##############################//
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <errno.h>
#include <sys/queue.h>
#include <list>
#include <rte_memory.h>
#include <rte_memzone.h>
#include <rte_launch.h>
#include <rte_eal.h>
#include <rte_per_lcore.h>
#include <rte_lcore.h>
#include <rte_debug.h>
#include <rte_common.h>
#include <rte_vect.h>
#include <rte_byteorder.h>
#include <rte_log.h>
#include <rte_memory.h>
#include <rte_memcpy.h>
#include <rte_memzone.h>
#include <rte_eal.h>
#include <rte_per_lcore.h>
#include <rte_launch.h>
#include <rte_atomic.h>
#include <rte_cycles.h>
#include <rte_prefetch.h>
#include <rte_lcore.h>
#include <rte_per_lcore.h>
#include <rte_branch_prediction.h>
#include <rte_interrupts.h>
#include <rte_pci.h>
#include <rte_random.h>
#include <rte_debug.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_ring.h>
#include<rte_spinlock.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>
#include <rte_ip.h>
#include <rte_tcp.h>
#include <rte_udp.h>
#include <rte_rtp.h>
#include <rte_fec.h>
#include <rte_ring.h>
#include <rte_hash.h>
#include <rte_hash_crc.h>
#define DEFAULT_HASH_FUNC       rte_hash_crc
// rtp and fec header are directly include in build/include/
bool lock = false;
// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
const char *file_name = "/home/waqas/Downloads/rtp-stream.pcap";
pcap_t *pt, *ptr;
uint64_t buffer_size = 1048576;
// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
#define RTP 0
#define FEC 1
#define OTHER 2
#define IGMP 3
//#define clear() printf("\033[H\033[J")
static volatile bool force_quit;
uint32_t groupAdd = 0, igmpSourceIp = 0;
int L=0, D=0;
int fec_leaving = 0;
static void printStats();
bool igmpPacket(struct rte_mbuf * igmpPkt);
void makeUdpPacket(struct rte_mbuf *created_pkt);
uint8_t packetType( struct rte_mbuf *pkt );
uint8_t getProtocol( struct rte_mbuf *pkt );
uint32_t getSourceIp( struct rte_mbuf *pkt );
uint32_t getDestinationIp( struct rte_mbuf *pkt );
uint16_t getSourcePort( struct rte_mbuf *pkt );
uint16_t getDestinationPort( struct rte_mbuf *pkt );
int sendPacket(struct rte_mbuf **mbuf, int port);
int sendPacketQ(struct rte_mbuf **mbuf, int port);
#define NUM_OF_LCORES 8
#define NB_MBUF             (8192*8)
#define MAX_PKT_BURST       32
#define NB_SOCKETS          2
#define MEMPOOL_CACHE_SIZE  256

#define MC_IP_1       13
#define MC_IP_2       6
#define MC_IP_3       53
#define MC_IP_4       225

#define BOND_IP_1       0
#define BOND_IP_2       0
#define BOND_IP_3       0
#define BOND_IP_4       10
static rte_spinlock_t spinlock_conf[2] = {RTE_SPINLOCK_INITIALIZER};
struct MarkDataSymbols
{
	bool Mark;
	struct rte_mbuf *pkt; 
};

// uint32_t bond_ip = BOND_IP_1 | (BOND_IP_2 << 8) | (BOND_IP_3 << 16) | (BOND_IP_4 << 24);
uint32_t mc_ip = MC_IP_1 | (MC_IP_2 << 8) | (MC_IP_3 << 16) | (MC_IP_4 << 24);
static struct ether_addr ports_eth_addr[2];  // defined already RTE_MAX_ETHPORTS = 32
static struct ether_addr mc_eth_addr[2];
/*
 * Configurable number of RX/TX ring descriptors
 */
#define RTE_TEST_RX_DESC_DEFAULT 128
#define RTE_TEST_TX_DESC_DEFAULT 512
static uint16_t nb_rxd = RTE_TEST_RX_DESC_DEFAULT;
static uint16_t nb_txd = RTE_TEST_TX_DESC_DEFAULT;
static struct rte_mempool * pktmbuf_pool[NB_SOCKETS];
char ip4Address[20], sourceIpStr[20];
uint32_t multiCastIp = 0;
uint32_t sourceIp = 0;
uint32_t ports = 1;
uint32_t BLOCKS = 2;
int packetMiss = 0;
int notSent = 0;
int c_count = 0;
struct lcore_para
{
	struct rte_ring *worker_rx;
	struct rte_ring *worker_tx;
	int missed_x;
	int missed_tx;
	int blocks;
	uint64_t pktcount;
//	bool force_quit;
};
struct SourceGroup
{
	uint32_t sourceAdd;
	uint32_t groupAdd;
	uint32_t old_groupAdd;
	uint16_t srcPort;
	uint16_t dstPort;
	bool set;
}NewAddresses[8];
/*
 * Construct Ethernet multicast address from IPv4 multicast address.
 * Citing RFC 1112, section 6.4:
 * "An IP host group address is mapped to an Ethernet multicast address
 * by placing the low-order 23-bits of the IP address into the low-order
 * 23 bits of the Ethernet multicast address 01-00-5E-00-00-00 (hex)."
 */
#define	ETHER_ADDR_FOR_IPV4_MCAST(x)	\
	(rte_cpu_to_be_64(0x01005e000000ULL | ((x) & 0x7fffff)) >> 16)
// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
struct iState
{
	int ID;        // record id  
	uint8_t port;
	uint32_t groupAddress;
	std::list <uint32_t> source_list_include;
	std::list <uint32_t> source_list_exclude;
	//static struct rte_timer gen;  
};
std::list<struct iState> InterfaceState;
static struct rte_timer gen[10], timer_gen;
bool packetMbufsSource(struct rte_mbuf **, int );
uint32_t parseIPV4string(char *ipAddress)
{
	//printf("strlen = %d\n", strlen(ipAddress));
	//puts(ipAddress);
	uint32_t ipbyte[4];
	//uint32_t ipbyte0 = 0, ipbyte1 = 0, ipbyte2 = 0, ipbyte3 = 0;
	//sscanf(ipAddress, "%uhh.%uhh.%uhh.%uhh", &ipbyte3, &ipbyte2, &ipbyte1, &ipbyte0);
	char arr[5] = {'\0','\0','\0','\0', '\0'};
	int x = 0, ind = 3, indarr = 0;
	int len;
	while(  x<strlen(ipAddress) )  
	{
		while(  ipAddress[x] != '.' )
		{
			arr[indarr]=ipAddress[x];
			x++;
			indarr++;
			if(ipAddress[x] == '\0')
				break;
			//printf("x = %d\n", x);
		}
		
		
		indarr++;
		arr[indarr] = '\0';
		ipbyte[ind--] = atoi(arr);
		//printf("atoi = %d\n", atoi(arr));
		indarr = 0;
		arr[0] = '\0';
		arr[1] = '\0';
		arr[2] = '\0';
		arr[3] = '\0';
		if((ipAddress[x]) == '\0')
			break;
		x++;
		
	}
	
	//printf("\nipbyte[0] = %d\n", ipbyte[0]);
	//printf("ipbyte[1] = %d\n", ipbyte[1]);
	//printf("ipbyte[2] = %d\n", ipbyte[2]);
	//printf("ipbyte[3] = %d\n", ipbyte[3]);
	
	uint32_t ipadd = ipbyte[0] | (ipbyte[1] << 8) | (ipbyte[2] << 16) | (ipbyte[3] << 24);
	return ipadd;
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
static int parse_args(int argc, char **argv)
{
	struct iState iStateObj1;
	int opt, ret, n, id = 0, st = 0, en = 0, k;
	char str[10];
	char **argvopt;
	int option_index = 0;
	char *prgname = argv[0];
	static struct option lgopts[] = { {NULL, 0, 0, 0} };
	argvopt = argv;
	while(( opt = getopt_long(argc, argvopt, "m:p:b:s:L:D:S:M:", lgopts, &option_index))  != EOF)
	{
		switch(opt)
		{
			case 'm':
				strcpy(ip4Address, optarg);
				puts(ip4Address);
				multiCastIp = parseIPV4string(ip4Address);
				printf("multiCastIp: %x \n",multiCastIp);
			break;
			case 's':
				strcpy(sourceIpStr, optarg);
				sourceIp = parseIPV4string(sourceIpStr);
				
			break;
			case 'S':
				strcpy(sourceIpStr, optarg);
				igmpSourceIp = parseIPV4string(sourceIpStr);
				
			break;	
				
			case 'p':
				printf("we are in option p\n");
				ports = atoi(optarg);
			break;
			case 'b':
				BLOCKS = atoi(optarg);
				printf("BLOCKS = %d\n", BLOCKS);
				//sleep(2);
				break;
			case 'L':
				L = atoi(optarg);
				break;
			case 'D':
				D = atoi(optarg);
				break;
			case 'M':
			for(n = 1; n < argc; n++)
				{
					if( strcmp(argv[n], "-M") == 0)
					{
						while( n < argc)
						{
							st = n+1;
							en = st;
							if( (st >= argc) || strlen(argv[st])==2 )
								break;
							for(k = st+1; k<argc; k++)
							{
								ret = IS_IPV4_MCAST(parseIPV4string(argv[k]));
								//printf("multicast IP: %d\n", ret);
								if(ret == 0 && strlen(argv[k])>6)
								{
									en = en + 1;
								}
								else
									break;
							}
							for(k = st; k<=en; k++)
							{
								//printf("k =  %d: ", k);
								//puts(argv[k]);
								//sleep(5);
								ret = IS_IPV4_MCAST(parseIPV4string(argv[k]));
								if(ret == 1)
								{
									iStateObj1.ID = id++;
									iStateObj1.groupAddress = parseIPV4string(argv[k]);
								}
								else
								{
									iStateObj1.source_list_include.push_back(parseIPV4string(argv[k]));
								}
							}
							InterfaceState.push_back(iStateObj1);
							iStateObj1.source_list_include.clear();
							//iStateObj1.groupAddress = 0;
							n = en;
							
							//printf("\t\tst %d, en %d, argc %d\n", st, en, argc);
							puts(argv[n]);
							//sleep(1);
							
							//puts(argv[n]);
							
						}
					}
				}	
			break;	
			default:
				printf("please enter valid options!!\n");	
		}
	}
	return 0;
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
//              				HASH STRUCTS FUNCTIONS
void populate_hash_table_with_multicast_add(void);
struct ipv4_5tuple {
        uint32_t ip_dst;
        uint32_t ip_src;
        uint16_t port_dst;
        uint16_t port_src;
        uint8_t  proto;
} __attribute__((__packed__));

struct ipv4_l3fwd_route {
	struct ipv4_5tuple key;
	uint8_t if_out;
};

static struct ipv4_l3fwd_route ipv4_l3fwd_route_array[] = 
{
	{{IPv4(225,53,6,13), IPv4(10,177,6,13),  8234, 1234, IPPROTO_UDP}, 0},
	{{IPv4(227,2,3,4), IPv4(200,20,0,1),  102, 12, IPPROTO_TCP}, 1},
	{{IPv4(229,1,1,1), IPv4(100,30,0,1),  101, 11, IPPROTO_TCP}, 2},
	{{IPv4(231,1,2,8), IPv4(200,80,0,1),  102, 15, IPPROTO_TCP}, 3},
	{{IPv4(235,1,2,8), IPv4(100,10,0,1),  101, 14, IPPROTO_TCP}, 4},
	{{IPv4(229,2,3,4), IPv4(200,50,0,1),  110, 13, IPPROTO_TCP}, 5},
	{{IPv4(227,1,1,2), IPv4(100,30,0,1),  120, 12, IPPROTO_TCP}, 6},
	{{IPv4(225,2,2,2), IPv4(101,40,0,1),  130, 12, IPPROTO_TCP}, 7},	
};
#define L3FWD_HASH_ENTRIES	16
typedef struct rte_hash lookup_struct_t;
static lookup_struct_t *ipv4_l3fwd_lookup_struct[1];
static uint8_t ipv4_l3fwd_out_if[L3FWD_HASH_ENTRIES] __rte_cache_aligned;
static struct lcore_para lcore_para[NUM_OF_LCORES] = { NULL }; 

#define IPV4_L3FWD_NUM_ROUTES \
	(sizeof(ipv4_l3fwd_route_array) / sizeof(ipv4_l3fwd_route_array[0]))
static void
print_ipv4_key(struct ipv4_5tuple key)
{
	printf("IP dst = %08x, IP src = %08x, port dst = %d, port src = %d, "
		"proto = %d\n", (unsigned)key.ip_dst, (unsigned)key.ip_src,
				key.port_dst, key.port_src, key.proto);
}
/*              %%%%%%%%%%%%%%%%%%%%%%%             */
void populate_hash_table_with_multicast_add( void )
{
	uint32_t _source_address = IPv4(172,16,1,2);
	uint32_t _group_address = IPv4(232,100,0,1);
	int ret, testAvailableLcores = 3, n = 1, port = 0;
	struct ipv4_5tuple key_test;
	std::list<uint32_t>::iterator li;
	std::list<struct iState>::iterator iter;
	iter = InterfaceState.begin();
	while(iter != InterfaceState.end())
	{
		li = iter->source_list_include.begin();
		key_test.ip_dst = iter->groupAddress;
		//key_test.ip_src = iter->source_list_include.pop_front();
		key_test.ip_src = *li;
		key_test.port_dst         = 0;
		key_test.port_src         = 0;
		key_test.proto            = IPPROTO_UDP;
		if(iter->source_list_include.size() > 1)
		{
			rte_exit(EXIT_FAILURE, "hash table is not supported yet for multiple source lists\n");
		}	
		ret = rte_hash_add_key ((rte_hash *)ipv4_l3fwd_lookup_struct[0], (void *) &key_test);
		printf("-1\n");
		if (ret < 0) 
		{
			rte_exit(EXIT_FAILURE, "Unable to add entry to the"
						"l3fwd hash on socket\n");
		}
		// testAvailableLcores: starts from lcore 3
		ipv4_l3fwd_out_if[ret] = testAvailableLcores;
		NewAddresses[testAvailableLcores].sourceAdd = htonl(_source_address);
		NewAddresses[testAvailableLcores].groupAdd = htonl(_group_address + IPv4(0,0,n,0));
		NewAddresses[testAvailableLcores].srcPort  = htons(22000 + port);
		NewAddresses[testAvailableLcores].dstPort  = htons(59001 + port);
		NewAddresses[testAvailableLcores].old_groupAdd = htonl(iter->groupAddress);
		//NewAddresses[testAvailableLcores].groupAdd = htonl(_group_address + IPv4(0,10*n,0,0));
		testAvailableLcores+=1;
		iter++;
		n++;
		port = port + 10;
	}
	// {{IPv4(231,1,2,8), IPv4(200,80,0,1),  102, 15, IPPROTO_TCP}, 3},
}
static void
setup_hash(int socketid)
{
	static struct rte_hash_parameters ipv4_l3fwd_hash_params;
	ipv4_l3fwd_hash_params.name = NULL,
	ipv4_l3fwd_hash_params.entries = L3FWD_HASH_ENTRIES,
	ipv4_l3fwd_hash_params.key_len = sizeof(struct ipv4_5tuple),
	ipv4_l3fwd_hash_params.hash_func = DEFAULT_HASH_FUNC,
	ipv4_l3fwd_hash_params.hash_func_init_val = 0;
	
	unsigned i;
	int ret;
	char s[64];

	/* create ipv4 hash */
	snprintf(s, sizeof(s), "ipv4_l3fwd_hash_%d", socketid);
	ipv4_l3fwd_hash_params.name = s;
	ipv4_l3fwd_hash_params.socket_id = socketid;
	ipv4_l3fwd_lookup_struct[socketid] =
		rte_hash_create(&ipv4_l3fwd_hash_params);
	printf("hash created \n");
	//sleep(1);
	if (ipv4_l3fwd_lookup_struct[socketid] == NULL)
		rte_exit(EXIT_FAILURE, "Unable to create the l3fwd hash on "
				"socket %d\n", socketid);
	populate_hash_table_with_multicast_add();
	printf("SS\n");
	//print_ipv4_key(ipv4_l3fwd_route_array[i].key);
}

int setup_lcore_parameters(void)
{
	char worker_rx[][15] = {"worker_rx00", "worker_rx01", "worker_rx02", "worker_rx03", "worker_rx04", "worker_rx05", "worker_rx06", "worker_rx07"};
	char worker_tx[][15] = {"worker_tx00", "worker_tx01", "worker_tx02", "worker_tx03", "worker_tx04", "worker_tx05", "worker_tx06", "worker_tx07"};
	int x;
	for(x = 0; x < NUM_OF_LCORES; x++)
	{
		puts(&worker_rx[x][0]);
		lcore_para[x].worker_rx = rte_ring_create(&worker_rx[x][0], 128, 0, 
												 RING_F_SP_ENQ | RING_F_SC_DEQ);
		lcore_para[x].worker_tx = rte_ring_create(&worker_tx[x][0], 128, 0, 
												 RING_F_SP_ENQ | RING_F_SC_DEQ);
		if(lcore_para[x].worker_rx == NULL || lcore_para[x].worker_tx == NULL)
		{
			rte_exit(EXIT_FAILURE, "Unable to create ring %d\n", x);
		}
		lcore_para[x].missed_x = 0;
		lcore_para[x].missed_tx = 0;
		lcore_para[x].blocks   = 0;
		lcore_para[x].pktcount = 0;
	}
}
bool buildKeyFromPacket(struct ipv4_5tuple *key_test, struct rte_mbuf *data_pkt)
{
	uint32_t destIp;
	uint16_t protocol = 0;
	protocol = getProtocol(data_pkt);
	if(protocol == 17)
	{
		// udp packet
		destIp = getDestinationIp(data_pkt);
		if(IS_IPV4_MCAST(destIp) == 0)
		{
			//printf("not a multicast ?\n");
			return false;
		}
		key_test->ip_dst   = destIp; 
		key_test->ip_src   = getSourceIp(data_pkt);
		key_test->port_dst = 0; //getDestinationPort(data_pkt);
		key_test->port_src = 0; //getSourcePort(data_pkt);
		key_test->proto    = getProtocol(data_pkt);
		return true;
	}
	else
	{
		return false;
	}
}
void assignNewIpSourceGroup(struct rte_mbuf * pkt, int lcore_id)
{
	struct ipv4_hdr *iph;
	struct udp_hdr *udp;
	iph = (struct ipv4_hdr *)(rte_pktmbuf_mtod(pkt, char *) + sizeof(struct ether_hdr)); 
	uint16_t ip_hdr_length = (iph->version_ihl & 0x0f)*4;
	udp = (struct udp_hdr *)(rte_pktmbuf_mtod(pkt, char *) + sizeof(struct ether_hdr) + ip_hdr_length);
	
	iph->src_addr = NewAddresses[lcore_id].sourceAdd;
	iph->dst_addr = NewAddresses[lcore_id].groupAdd;
	iph->hdr_checksum = 0;
	iph->hdr_checksum = (rte_ipv4_cksum(iph));
	
	udp->src_port = NewAddresses[lcore_id].srcPort;
	udp->dst_port = NewAddresses[lcore_id].dstPort;
	
		
}
static int
lcore_Distributer(void)
{
	unsigned lcore_id, lcoreID;
	bool timerSet = false;
	bool k;
	uint8_t type;
	int ret, numPackets, count=0;
	struct rte_mbuf *data_pkt[MAX_PKT_BURST];
	struct ipv4_5tuple key_test;
	lcore_id = rte_lcore_id();
	printf("hello from Distributer lcore %u\n", lcore_id);
	// ret = function_hash();
	setup_lcore_parameters();
	int missed = 0;
	while(!force_quit)
	{
		// port id, Queue id
		numPackets = rte_eth_rx_burst(0, 0, data_pkt, MAX_PKT_BURST);
		for(int x = 0; x < numPackets; x++)
		{
			rte_vlan_strip(data_pkt[x]);
			//assignNewIpSourceGroup(data_pkt[x], (int)lcore_id);
			//rte_eth_tx_burst(1, 0, &data_pkt[x], 1);
			//while(1);
			type = packetType(data_pkt[x]);     // 0 = rtp, 1 = fec, 2 = other
			//printf("%d:type = %d\n", count++, type);
			k = buildKeyFromPacket(&key_test, data_pkt[x]);
			if(k == true)
			{
				/* first we lookup into hash table! if not found we add it into H table */
				ret = rte_hash_lookup(ipv4_l3fwd_lookup_struct[0], (const void *)&key_test);
				if(ret < 0)
				{
					//printf("not a valid hash stream: putting in 1 %d \n", missed++);
					int r = rte_ring_sp_enqueue(lcore_para[1].worker_rx, (void *)data_pkt[x]);
					if(r!=0)
					{
						//printf("missed =  %d \n", missed++);
						lcore_para[1].missed_x += 1;
					}
					
				}
				else if(ret >= 0)
				{
					/* key already in hash table! */
					lcoreID = ipv4_l3fwd_out_if[ret];
					//printf("MC hash lcoreID %d\n", lcoreID);
					int n = rte_ring_sp_enqueue(lcore_para[lcoreID].worker_rx, (void *)data_pkt[x]); 
					if(n!=0)
					{
						//printf("missed =  %d, %u\n", missed++, lcoreID);
						lcore_para[lcoreID].missed_x += 1;
					}
				}
			}
			else
			{
				//rte_pktmbuf_free(data_pkt[x]);
				int r = rte_ring_sp_enqueue(lcore_para[1].worker_rx, (void *)data_pkt[x]);
				if(r!=0)
				{
					//printf("missed =  %d \n", missed++);
					lcore_para[1].missed_x += 1;
				}
			}
		}
	}
	printStats();
	return ret;
}
/// %%%%%%%%%%-------End of Distributer Lcore functions--------%%%%%%%%%%%%%%%%%%%////
static int
lcore_IGMP(void)
{
	bool timerSet = false, exitFromLoop = true;
	int numPackets = 0;
	uint8_t type;
	unsigned lcore_id;
	lcore_id = rte_lcore_id();
	struct rte_mbuf *data_pkt[MAX_PKT_BURST];
	//sleep(4);
	printf("hello from lcore_IGMP %u\n", lcore_id);
	printf(" \n");
	void *pkts[64];
	
	while(!force_quit)
	{
	       rte_timer_manage();	
		//printf("lcore_para[2].worker_rx == NULL :%d \n", lcore_para[2].worker_rx == NULL);
		//printf("rte_ring_empty(lcore_para[2].worker_rx) != 1 :%d \n", rte_ring_empty(lcore_para[2].worker_rx) != 1);
		if(lcore_para[1].worker_rx != NULL)
		{
			numPackets = rte_ring_dequeue_burst(lcore_para[1].worker_rx, pkts,32, NULL);
			if(numPackets)
			{
				//printf("numPackets = %d\n", numPackets);
				for(int k = 0; k<numPackets; k++)
				{
					data_pkt[k] = (struct rte_mbuf *)pkts[k];
					type = packetType(data_pkt[k]);
					if(type == IGMP)
					{
						timerSet = igmpPacket(data_pkt[k]);
						lcore_para[1].pktcount +=1;
						system("clear");
						printStats();
					}
					else
						rte_pktmbuf_free(data_pkt[k]);
				}
					//numPackets = 0;
			}
		}
		else
		{
			//printf("Nothing in IGMP ring \n");
		}
	}
}
static void IptoString(uint32_t ipadd)
{
	uint32_t IP1, IP2, IP3, IP4;
	uint32_t mask1, mask2, mask3, mask4;
	mask1 = 0x000000ff;
	mask2 = 0x0000ff00;
	mask3 = 0x00ff0000;
	mask4 = 0xff000000;
	IP4 = (ipadd & mask4)>>24;
	IP3 = (ipadd & mask3)>>16;
	IP2 = (ipadd & mask2)>>8;
	IP1 = (ipadd & mask1);
	printf("%d.%d.%d.%d\n", IP1, IP2, IP3, IP4);
}
static void printStats()
{
	printf("============ Packet Lost Statistics ===============\n");
	for(int x = 0; x < NUM_OF_LCORES; x++)
	{
		if(x!=1)
		{
			printf("LCORE_ID [ %d ] m_rx:%d, m_tx:%d, blocks:%d\n", x, lcore_para[x].missed_x, lcore_para[x].missed_tx, lcore_para[x].blocks);
			if(x>=3)
			{
				printf("Encoding -> [new][old]\n");
				IptoString(NewAddresses[x].groupAdd);
				IptoString(NewAddresses[x].old_groupAdd);
			}
		}
		else
		{
			printf("LCORE_ID [ %d ] pktcount:%d, m_rx:%d, m_tx:%d, blocks:%d\n", x, lcore_para[x].pktcount, lcore_para[x].missed_x,lcore_para[x].missed_tx, lcore_para[x].blocks);
		}
	
	}
}
static int
lcore_TX(void)
{
	/* get all sorts of Tx packets and send them to ports */
	unsigned lcore_id;
	lcore_id = rte_lcore_id();
	printf("hello from lcore_TX %u\n", lcore_id);
	printf(" \n");
	int x;
	unsigned count = 0;
	unsigned int available = 0;
	void *pkts[64];
	while(!force_quit)
	{
		for(x = 0; x < NUM_OF_LCORES; x++)
		{
			if(lcore_para[x].worker_tx == NULL)
				continue;
			count = rte_ring_sc_dequeue_burst(lcore_para[x].worker_tx, (void **)pkts, 32, NULL);
			for(int n = 0; n < count; n++)
			{
				int sent = sendPacket((struct rte_mbuf **)&pkts[n], 0);
			//	printf("sending lcore = %d, status = %d\n", x, sent);
			}
			//printf("lcore-Tx loop\n");
		}
	}
	
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////

uint16_t calc_checksum(uint16_t *buf, int length)
{
    uint64_t sum;

    // checksum is calclated by 2 bytes
    for (sum=0; length>1; length-=2) 
        sum += *buf++;

    // for an extra byte
    if (length==1)
        sum += (char)*buf;

    // this can calc the 1's complement of the sum of each 1's complement
    sum = (sum >> 16) + (sum & 0xFFFF);  // add carry
    sum += (sum >> 16);          // add carry again
    return ~sum;
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
static void print_ethaddr(const char *name, const struct ether_addr *eth_addr)
{
	char buf[ETHER_ADDR_FMT_SIZE];
	ether_format_addr(buf, ETHER_ADDR_FMT_SIZE, eth_addr);
	printf("%s%s", name, buf);
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
int sendPacket(struct rte_mbuf **mbuf, int port)
{
	int ret;
	//e_spinlock_lock(&spinlock_conf[port]);
	ret = rte_eth_tx_burst(port, 0, mbuf, 1);
	if(ret <= 0)
	{
		notSent++;
		//printf("Packet Not sent\n");
	}
	else
	{
		//printf("Packet sent %d\n", ret);
	}
	//e_spinlock_unlock(&spinlock_conf[port]);
	//rte_pktmbuf_free(*mbuf);
	return ret;
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
int insertVlanTag(struct rte_mbuf *mbuf)
{
	rte_vlan_insert(&mbuf);
	struct ether_hdr *eth_hdr;
	struct vlan_hdr *vlh;
	vlh = (struct vlan_hdr*)(rte_pktmbuf_mtod(mbuf, char*)+sizeof(struct ether_hdr));
	vlh->vlan_tci = htons(49172); //49172(vlan100)	
	return 0;
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
void constIgmpPacket(struct rte_mbuf *created_pkt, int queryType, uint32_t groupAddress)
{
	// test code for inserting source and GA into Membership reports //
	union {
		uint64_t as_int;
		struct ether_addr as_addr;
	} mc_eth_addr1;
	int nSources;
	groupAddress = groupAdd;
	//list <string> source_list_include
	std::list <uint32_t>::iterator li;
	std::list<struct iState>::iterator iter, iter2;
	iter = InterfaceState.begin();
	uint16_t numberOfGroupRecords = InterfaceState.size();
	nSources = iter->source_list_include.size();
	// calculating size of payload of igmp packet
	int tempPayload = 0;
	while(iter != InterfaceState.end())
	{
		if(queryType == GENERAL_QUERY)
		{
			// for each GroupAddress + Rec Type + Aux data Len + Numb of Sources fields
			tempPayload = tempPayload + 8; 
			// for each source list size belong to specific Group Record
			tempPayload = tempPayload + (iter->source_list_include.size())*4; 
			iter++;
			//printf("tempPaload size  = %d\n", tempPayload);
		}
		if(queryType == GROUP_QUERY)
		{
			if(groupAddress == iter->groupAddress)
			{
				// for each GroupAddress + Rec Type + Aux data Len + Numb of Sources fields
				tempPayload = tempPayload + 8; 
				// for each source list size belong to specific Group Record
				tempPayload = tempPayload + (iter->source_list_include.size())*4; 
				iter++;
				numberOfGroupRecords = 1;
				break;  // because only one such record should exist for particular group
			}
		}
	}
	uint8_t *payload1, *payload2;
	struct ether_hdr *eth_hdr;
    struct ipv4_hdr *ip_hdr;
	struct igmpv3_hdr *igmpv3;
	struct groupRecord *gRec;
	uint32_t *nS;
	uint32_t bond_ip = BOND_IP_1 | (BOND_IP_2 << 8) | (BOND_IP_3 << 16) | (BOND_IP_4 << 24);
	size_t pkt_size;
	pkt_size = sizeof(struct ether_hdr) + sizeof(struct ipv4_hdr) + sizeof(struct igmpv3_hdr)
																  + tempPayload;
																  //+ sizeof(struct groupRecord)
	    														  //+ sizeof(uint32_t)*nSources; 
	//TODO: only for 1 source and 1 group record. 
	//printf("pkt_size %d\n", pkt_size);
	created_pkt->data_len = pkt_size;
    created_pkt->pkt_len = pkt_size;
	eth_hdr = rte_pktmbuf_mtod(created_pkt, struct ether_hdr *);
	eth_hdr->ether_type = rte_cpu_to_be_16(ETHER_TYPE_IPv4);
	rte_eth_macaddr_get(0, &ports_eth_addr[0]);
	ether_addr_copy(&ports_eth_addr[0], &eth_hdr->s_addr);
	//print_ethaddr(" [i]dst Address: ", &eth_hdr->d_addr);	
	ip_hdr = (struct ipv4_hdr *)(rte_pktmbuf_mtod(created_pkt, char *) + sizeof(struct ether_hdr));
	ip_hdr->version_ihl = 0x45;
	ip_hdr->type_of_service = 0xc0;
	ip_hdr->total_length = htons(pkt_size-sizeof(struct ether_hdr));  
	ip_hdr->packet_id = 1;
	ip_hdr->fragment_offset = htons(0x4000);
	ip_hdr->time_to_live = 1;
	ip_hdr->next_proto_id = 2;
	ip_hdr->hdr_checksum  =  0;
	ip_hdr->src_addr = htonl(igmpSourceIp);             
	if(queryType == GENERAL_QUERY || queryType == GROUP_SOURCE_QUERY)
	{
		ip_hdr->dst_addr = htonl(parseIPV4string("224.0.0.22"));
		mc_eth_addr1.as_int = ETHER_ADDR_FOR_IPV4_MCAST((parseIPV4string("224.0.0.22")));
	}
	else if(queryType == GROUP_QUERY)
	{
		ip_hdr->dst_addr = htonl(groupAddress);
		mc_eth_addr1.as_int = ETHER_ADDR_FOR_IPV4_MCAST(groupAddress);
	}
	ether_addr_copy(&mc_eth_addr1.as_addr, &eth_hdr->d_addr);
	ip_hdr->hdr_checksum = rte_ipv4_cksum(ip_hdr);
	
	
	igmpv3 = (struct igmpv3_hdr *)(rte_pktmbuf_mtod(created_pkt, char *) 
							            + sizeof(struct ether_hdr) 
							            + sizeof(struct ipv4_hdr));
	payload1 = (uint8_t *)(rte_pktmbuf_mtod(created_pkt, char *) 
							            + sizeof(struct ether_hdr) 
							            + sizeof(struct ipv4_hdr)) 
										+ sizeof(struct igmpv3_hdr);
	payload2 = (uint8_t *)(rte_pktmbuf_mtod(created_pkt, char *) 
							            + sizeof(struct ether_hdr) 
							            + sizeof(struct ipv4_hdr)) 
										+ sizeof(struct igmpv3_hdr)
										+ sizeof(struct groupRecord);
	igmpv3->type = 0x22;
	igmpv3->reserved1 = htons(0);
	igmpv3->checksum = htons(0);
	igmpv3->reserved2 = htons(0);
	igmpv3->nGroupRecords = htons(numberOfGroupRecords);    
	uint32_t *sources;
	//printf("tempPayload: %d, groupAddress: %x, NR: %d\n", tempPayload, groupAddress, htons(igmpv3->nGroupRecords));
	// gothrough all ports or interfaces
	iter = InterfaceState.begin();
	while(iter != InterfaceState.end())
	{
		if(queryType == GROUP_QUERY)
		{
			
			if(groupAddress != iter->groupAddress)
			{
				iter++;
				continue;
			}
			// In case of unmatched groupAdd we should skip that (all) records
		}
		gRec = (struct groupRecord*)payload1;
		if(iter->source_list_include.size() == 0)
			gRec->rtype = 2; // MODE_IS_EXCLUDE;
		else
			gRec->rtype = 1; // MODE_IS_INCLUDE;
		gRec->auxDataLen = 0;
		gRec->nSources = htons(iter->source_list_include.size());
		gRec->multiCastAdd = htonl(iter->groupAddress);
		//printf("XXXXXXXXXXX groupAddress  = %x , tempPayload %d\n", htonl(iter->groupAddress), tempPayload);
		payload1 = (uint8_t*)payload1 + sizeof(struct groupRecord);
		sources = (uint32_t*)payload1;
		li = iter->source_list_include.begin();
		while(li != iter->source_list_include.end()) 
		{
			*sources = htonl(*li);
			sources = sources + 1;
			//printf("%x \n", htonl(*li));
			li++;
		}
		//printf("nSources = %d\n", nSources);
		iter++;
		payload1 = (uint8_t*)sources;
		
	}
	igmpv3->checksum = calc_checksum((uint16_t*)igmpv3, sizeof(struct igmpv3_hdr) + tempPayload);
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
/* timer0 callback */
static void
IgmpV3GeneralQueryReport(__attribute__((unused)) struct rte_timer *tim,
	  							__attribute__((unused)) void *arg)
{
	//printf("\t\tinto fun: IgmpV3GeneralQueryReport\n");
	int nSources;
	uint32_t groupAdd;
	unsigned lcore_id = rte_lcore_id();
	//printf("%s() on lcore %u\n", __func__, lcore_id);
	struct rte_mbuf *mbuf;
	if(packetMbufsSource(&mbuf, 1))
	{
		constIgmpPacket(mbuf, GENERAL_QUERY, 0);
		int ret = insertVlanTag(mbuf);
		if(!sendPacketQ(&mbuf, 0))
		{
			//printf("REPORT SENT\n");
		}
		else
			printf("REPORT NOT SENT\n");
	}
	return;
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
/* Group specific timer callback */
static void
IgmpV3GroupQueryReport(__attribute__((unused)) struct rte_timer *tim,
	  							__attribute__((unused)) void *arg)
{
	//uint32_t groupAdd = *((uint32_t *)arg);
	//printf("xxinto fun %x\n", groupAdd);
	int nSources;
	unsigned lcore_id = rte_lcore_id();
	//printf("%s() on lcore %u\n", __func__, lcore_id);
	struct rte_mbuf *mbuf;
	if(packetMbufsSource(&mbuf, 1))
	{
		constIgmpPacket(mbuf, GROUP_QUERY, 0);
		rte_vlan_insert(&mbuf);
		int ret = insertVlanTag(mbuf);
		if(sendPacketQ(&mbuf, 0))
		{//printf("REPORT SENT\n");
		}
		else
			printf("REPORT NOT SENT\n");
	}
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
/*   igmp control functions  */
uint8_t getResponseCode(struct rte_mbuf * igmpPkt, int igmpVersion)
{
	struct ipv4_hdr *iph;
	iph = (struct ipv4_hdr *)(rte_pktmbuf_mtod(igmpPkt, char *) + sizeof(struct ether_hdr));
	uint16_t ip_hdr_length = (iph->version_ihl & 0x0f)*4;
	if( (igmpVersion == GENERAL_QUERY_V2) || ( igmpVersion == GROUP_QUERY_V2) )
	{
		struct igmpv2Query *igmpv2query;	
		igmpv2query = (struct igmpv2Query *)(rte_pktmbuf_mtod(igmpPkt, char *) 
											+ sizeof(struct ether_hdr) 
											+ ip_hdr_length);
		//printf("getResponseCode1\n");
		return(igmpv2query->responseCode); 
	}
	else
	{
		struct igmpv3Query *igmpv3Query;	
		igmpv3Query = (struct igmpv3Query *)(rte_pktmbuf_mtod(igmpPkt, char *) 
											+ sizeof(struct ether_hdr) 
											+ ip_hdr_length);
		//printf("getResponseCode2\n");
		return(igmpv3Query->responseCode);
	}
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
int queryType(struct rte_mbuf * igmpPkt)
{
	struct ether_hdr *eth_hdr;
	struct ipv4_hdr *iph;
	iph = (struct ipv4_hdr *)(rte_pktmbuf_mtod(igmpPkt, char *) + sizeof(struct ether_hdr));
	uint16_t length = htons(iph->total_length) - (iph->version_ihl & 0x0f)*4;
	uint16_t ip_hdr_length = (iph->version_ihl & 0x0f)*4;
	//printf("htons(iph->total_length) = %d\n", htons(iph->total_length));
	//printf("(iph->version_ihl & 0x0f)*4 = %d\n", (iph->version_ihl & 0x0f)*4);
	if(length == 8)
	{
		struct igmpv2Query *igmpv2query;	
		igmpv2query = (struct igmpv2Query *)(rte_pktmbuf_mtod(igmpPkt, char *) 
											+ sizeof(struct ether_hdr) 
											+ ip_hdr_length);
		if(igmpv2query->type == 0x16 || igmpv2query->type == 0x17)
		{
			//printf("mbuf free\n");
			rte_pktmbuf_free(igmpPkt);
			return 5;
		}
		else if(htonl(igmpv2query->groupAdd) == 0)
			return 3; // general Query igmpv2
		else 
		{
			//printf("group add %x, sizeof(struct ipv4_hdr) = %d\n", htonl(igmpv2query->groupAdd), sizeof(struct ipv4_hdr));
			return 4; // group specific igmpv2 Query
		}
	}
	struct igmpv3Query *igmpv3Query;	
	igmpv3Query = (struct igmpv3Query *)(rte_pktmbuf_mtod(igmpPkt, char *) 
							            + sizeof(struct ether_hdr) 
							            + ip_hdr_length);
	if(igmpv3Query->type == 0x22)
	{
			rte_pktmbuf_free(igmpPkt);
			return 5;
	}
	else if(htonl(igmpv3Query->groupAdd) == 0)
		return 0; // general Query
	else if( (htonl(igmpv3Query->groupAdd) != 0) && (htons(igmpv3Query->nSources) == 0) )
		return 1; // group specific Query
	else if( (htonl(igmpv3Query->groupAdd) != 0) && (htons(igmpv3Query->nSources) != 0) )
		return 2; // group and source specific Query
	return 7;
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
uint32_t getGroupAddress(struct rte_mbuf * igmpPkt)
{
	struct ipv4_hdr *iph;
	iph = (struct ipv4_hdr *)(rte_pktmbuf_mtod(igmpPkt, char *) + sizeof(struct ether_hdr));
	uint16_t ip_hdr_length = (iph->version_ihl & 0x0f)*4;
	struct igmpv3Query *igmpv3Query;	
	igmpv3Query = (struct igmpv3Query *)(rte_pktmbuf_mtod(igmpPkt, char *) 
							            + sizeof(struct ether_hdr) 
							            + ip_hdr_length);
	return(htonl(igmpv3Query->groupAdd));
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
uint32_t getSourceAddress(struct rte_mbuf * igmpPkt)
{
	struct ipv4_hdr *iph;
	iph = (struct ipv4_hdr *)(rte_pktmbuf_mtod(igmpPkt, char *) + sizeof(struct ether_hdr));
	uint16_t ip_hdr_length = (iph->version_ihl & 0x0f)*4;
	struct igmpv3Query *igmpv3Query;
	uint8_t *temp;
	temp = (uint8_t *)(rte_pktmbuf_mtod(igmpPkt, char *) 
							            + sizeof(struct ether_hdr) 
							            + ip_hdr_length
										+ sizeof(struct igmpv3Query));	
	return(htonl(*((uint32_t *)temp)));
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
uint32_t findGroupRecord(struct rte_mbuf * igmpPkt)
{
	uint32_t groupAdd1 = getGroupAddress(igmpPkt);
	//printf("GroupAdd = %x", (groupAdd));
	std::list <uint32_t>::iterator li;
	std::list<struct iState>::iterator iter;
	iter = InterfaceState.begin();
	while(iter != InterfaceState.end())
	{
		if(iter->groupAddress == groupAdd1) 
			return (iter->groupAddress);
		iter++;
	}
	return 0;
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
uint32_t findGroupAndSourceRecord(struct rte_mbuf * igmpPkt)
{
	uint32_t groupAdd1 = getGroupAddress(igmpPkt);
	//printf("GroupAdd :findG= %x", (groupAdd1));
	std::list <uint32_t>::iterator li;
	std::list<struct iState>::iterator iter;
	iter = InterfaceState.begin();
	while(iter != InterfaceState.end())
	{
		if(iter->groupAddress == groupAdd1) 
		{
			li = iter->source_list_include.begin();
			while(li != iter->source_list_include.end()) 
			{
				if( getSourceAddress(igmpPkt) == *li )
					return(iter->groupAddress); 
				//printf("%x \n", htonl(*li));
				li++;
			}
		}
		iter++;
	}
	return 0;
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
int constIgmpv2Packet(struct rte_mbuf *created_pkt, int queryType, uint32_t groupAddress)
{
	union {
		uint64_t as_int;
		struct ether_addr as_addr;
	} mc_eth_addr1;
	struct ether_hdr *eth_hdr;
    struct ipv4_hdr *ip_hdr;
	struct igmpv2Query *igmpv2query;
	size_t pkt_size;
	pkt_size = sizeof(struct ether_hdr) + sizeof(struct ipv4_hdr) + sizeof(struct igmpv2Query);  
	//printf("pkt_size %d\n", pkt_size);
	created_pkt->data_len = pkt_size;
    created_pkt->pkt_len = pkt_size;
	eth_hdr = rte_pktmbuf_mtod(created_pkt, struct ether_hdr *);
	eth_hdr->ether_type = rte_cpu_to_be_16(ETHER_TYPE_IPv4);
	rte_eth_macaddr_get(0, &ports_eth_addr[0]);
	ether_addr_copy(&ports_eth_addr[0], &eth_hdr->s_addr);
	//print_ethaddr(" [i]dst Address: ", &eth_hdr->d_addr);	
	ip_hdr = (struct ipv4_hdr *)(rte_pktmbuf_mtod(created_pkt, char *) + sizeof(struct ether_hdr));
	ip_hdr->version_ihl = 0x45;
	ip_hdr->type_of_service = 0xc0;
	ip_hdr->total_length = htons(pkt_size-sizeof(struct ether_hdr));  
	ip_hdr->packet_id = 1;
	ip_hdr->fragment_offset = htons(0x4000);
	ip_hdr->time_to_live = 1;
	ip_hdr->next_proto_id = 2;
	ip_hdr->hdr_checksum  =  0;
	ip_hdr->src_addr = htonl(igmpSourceIp);             
	ip_hdr->dst_addr = htonl(groupAddress);
	mc_eth_addr1.as_int = ETHER_ADDR_FOR_IPV4_MCAST(groupAddress);
	ether_addr_copy(&mc_eth_addr1.as_addr, &eth_hdr->d_addr);
	ip_hdr->hdr_checksum = rte_ipv4_cksum(ip_hdr);
	igmpv2query = (struct igmpv2Query *)(rte_pktmbuf_mtod(created_pkt, char *) 
							            + sizeof(struct ether_hdr) 
							            + sizeof(struct ipv4_hdr));
	igmpv2query->type = 0x16;          // v2 membership report
	igmpv2query->responseCode = 0;
	igmpv2query->checksum = htons(0);
	igmpv2query->groupAdd = htonl(groupAddress);  // TODO
	igmpv2query->checksum = calc_checksum((uint16_t*)igmpv2query, sizeof(struct igmpv2Query));
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
/* V2 General Query Response timer callback */
static void
IgmpV2GeneralQueryReport(__attribute__((unused)) struct rte_timer *tim,
	  							__attribute__((unused)) void *arg)
{
	int *id = (int *)arg;
	std::list<struct iState>::iterator iter;
	iter = InterfaceState.begin();
	while(iter != InterfaceState.end())
	{
		if(iter->ID == *id)
		{
			break;
		}
		iter++;
	} 
	struct rte_mbuf *mbuf;
	if(packetMbufsSource(&mbuf, 1))
	{
		constIgmpv2Packet(mbuf, GENERAL_QUERY_V2, iter->groupAddress);
		int ret = insertVlanTag(mbuf);
		if(sendPacketQ(&mbuf, 0))
		{//printf("REPORT SENT %x\n", iter->groupAddress);
		}
		else
		{printf("REPORT NOT SENT\n");
		}
	}

}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
/* V2 General Specefic timer callback */
static void
IgmpV2GroupSpeceficReport(__attribute__((unused)) struct rte_timer *tim,
	  							__attribute__((unused)) void *arg)
{
	std::list<struct iState>::iterator iter;
	iter = InterfaceState.begin();
	while(iter != InterfaceState.end())
	{
		if(iter->groupAddress == groupAdd)
		{
			break;
		}
		iter++;
	} 
	struct rte_mbuf *mbuf;
	if(packetMbufsSource(&mbuf, 1))
	{
		constIgmpv2Packet(mbuf, GROUP_QUERY_V2, iter->groupAddress);
		int ret = insertVlanTag(mbuf);
		if(sendPacketQ(&mbuf, 0))
		{ //printf("REPORT SENT %x\n", iter->groupAddress);
		}
		else
		{printf("REPORT NOT SENT\n");
		}
	}

}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////
bool igmpPacket(struct rte_mbuf * igmpPkt)
{
	uint8_t maxResTimeX;
	int type = queryType(igmpPkt);
	//printf("query type %d\n", type);
	if(type == 5)
		return false;
	maxResTimeX = getResponseCode(igmpPkt, type);
	//printf("maxResTimeX = %d\n", maxResTimeX);
	if(maxResTimeX == 0)
		maxResTimeX = 100;
	float maxResTime = (float)(rand()%maxResTimeX)/10;
	//printf("type_QUERY %d,   maxResTime = %f, maxResTimeX = %d\n", type, maxResTime, maxResTimeX);
	//while(1);
	uint64_t hz;
	unsigned lcore_id;
	rte_timer_subsystem_init();
	hz = rte_get_timer_hz();
	lcore_id = rte_lcore_id();
	int n = 0;
	if(type == GENERAL_QUERY_V2)   
	{
		std::list<struct iState>::iterator iter;
		iter = InterfaceState.begin();
		while(iter != InterfaceState.end())
		{
			iter->ID = n;   // if it was not set already, used to id particular record
			rte_timer_init(&gen[n]);
			maxResTime = (float)(rand()%maxResTimeX)/10;
			rte_timer_reset(&gen[n++], maxResTime*hz, SINGLE, lcore_id, IgmpV2GeneralQueryReport, (void *)&iter->ID);
			iter->ID = iter->ID + 1;
		iter++;
		}
	
	}
	else if (type == GROUP_QUERY_V2)
	{
		//TODO IgmpV2GroupSpeceficReport
		groupAdd = findGroupRecord(igmpPkt);
		if( groupAdd != 0)
			rte_timer_reset(&gen[0], maxResTime*hz, SINGLE, lcore_id, IgmpV2GroupSpeceficReport, NULL);
			
	}
	else if(type == GENERAL_QUERY)
	{
		//printf("GENERAL_QUERY\n");
		//static struct rte_timer timer_gen;
		rte_timer_init(&timer_gen);
		//printf("--maxResTime*hz = %llu, hz = %llu\n", maxResTime*hz, hz);
		//while(1);
		rte_timer_reset(&timer_gen, maxResTime*hz, SINGLE, lcore_id, IgmpV3GeneralQueryReport, NULL);
		// PERIODICAL, SINGLE
	}
	else if(type == GROUP_QUERY)
	{
		static struct rte_timer timer_group;
		rte_timer_init(&timer_group);
		groupAdd = findGroupRecord(igmpPkt);
		//printf("--GroupAdd = %x\n", (groupAdd));
		if(groupAdd != 0)
		{
			rte_timer_reset(&timer_group, maxResTime*hz, SINGLE, lcore_id, IgmpV3GroupQueryReport, NULL);
		}
		else
			return false;
	}
	else if(type == GROUP_SOURCE_QUERY)
	{
		// groupAdd is global
		static struct rte_timer timer_group;
		rte_timer_init(&timer_group);
		groupAdd = findGroupAndSourceRecord(igmpPkt);
		//printf("xGROUP_SOURCE_QUERY %x\n", groupAdd);
		if(groupAdd != 0)
		{
			rte_timer_reset(&timer_group, maxResTime*hz, SINGLE, lcore_id, IgmpV3GroupQueryReport, NULL);
		}
		else
			return false;
	}
	else
	{
		rte_pktmbuf_free(igmpPkt);
		return false;
	}
	//rte_pktmbuf_free(igmpPkt);
	return true;
}
/// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%---------------%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%////


static int
init_mem(unsigned nb_mbuf)
{
	int socketid = 0;
	pktmbuf_pool[socketid] =
				rte_pktmbuf_pool_create("MBUF-POOL", nb_mbuf,
					                    MEMPOOL_CACHE_SIZE, 0,
					                    RTE_MBUF_DEFAULT_BUF_SIZE, socketid);
			if (pktmbuf_pool[socketid] == NULL)
				rte_exit(EXIT_FAILURE,
						"Cannot init mbuf pool on socket %d\n", socketid);
			else
				printf("Allocated mbuf pool on socket %d\n", socketid);
	return 0;

}

uint16_t getSequenceNumber(const u_char** pkt)
{
	struct rte_mbuf *created_pkt;
	struct ether_hdr *eth_hdr;
	struct ipv4_hdr *ip_hdr;
	struct udp_hdr *udp;
	struct rtp_hdr *rtp;
	created_pkt = (struct rte_mbuf *)pkt;
	rtp = (struct rtp_hdr *)(rte_pktmbuf_mtod(created_pkt, char *)
							            + sizeof(struct ether_hdr) 
							            + sizeof(struct ipv4_hdr)
										+ sizeof(struct udp_hdr));
	//printf("seqNumber: %d\n ",rte_cpu_to_be_16(rtp->seqNumber));
	return(rte_cpu_to_be_16(rtp->seqNumber));

}
uint16_t getSequenceNumberBase( struct rte_mbuf *pkt )
{
	struct fec_hdr *fec;
	fec = (struct fec_hdr *)(rte_pktmbuf_mtod(pkt, char *)
							+ sizeof(struct ether_hdr)
							+ sizeof(struct ipv4_hdr)
							+ sizeof(struct udp_hdr)
							+ sizeof(struct rtp_hdr));
	return(rte_cpu_to_be_16(fec->sequenceNumberBase));
}
uint8_t packetType( struct rte_mbuf *pkt )
{	
	//rte_vlan_strip(pkt);
	struct ether_hdr *eth_hdr;
	struct rtp_hdr *rtp;
	struct ipv4_hdr *iph;
	eth_hdr = rte_pktmbuf_mtod(pkt, struct ether_hdr *);
	if(rte_cpu_to_be_16(eth_hdr->ether_type) != ETHER_TYPE_IPv4)
	{
		//printf("vlan ...pkt\n");
		return OTHER;
	}
	iph = (struct ipv4_hdr *)(rte_pktmbuf_mtod(pkt, char *) + sizeof(struct ether_hdr));
	uint16_t ip_hdr_length = (iph->version_ihl & 0x0f)*4;
	rtp = (struct rtp_hdr *)(rte_pktmbuf_mtod(pkt, char *) 
							            + sizeof(struct ether_hdr) 
							            + ip_hdr_length
								    + sizeof(struct udp_hdr));
	//printf("check iph->next_proto_id = %d\n", iph->next_proto_id);
	if(iph->next_proto_id == 2)
		return IGMP;  // igmp packet 								  
	if(rtp->payloadT == 96)
	{
		return FEC;     // fec packet
	}
	else if(rtp->ver == 2 || rtp->ver == 1)
		return RTP;     // rtp packet
	else 						  
	{
		//printf("other .. pkt\n");
		return OTHER;     // other...
	}

}
uint32_t getTimeStamp(struct rte_mbuf *pkt)
{
	struct rtp_hdr *rtp;
	rtp = (struct rtp_hdr *)(rte_pktmbuf_mtod(pkt, char *) 
											+ sizeof(struct ether_hdr) 
											+ sizeof(struct ipv4_hdr)
											+ sizeof(struct udp_hdr));
	return(rte_cpu_to_be_32(rtp->timeStamp));	
}
void setTimeStamp(uint32_t tStamp, struct rte_mbuf *pkt)
{
	int lcore_id;
	lcore_id = (int)rte_lcore_id();
	struct fec_hdr *fec;
	fec = (struct fec_hdr *)(rte_pktmbuf_mtod(pkt, char *) 
							+ sizeof(struct ether_hdr) 
							+ sizeof(struct ipv4_hdr)
							+ sizeof(struct udp_hdr)
							+ sizeof(struct rtp_hdr));
	fec->timeStampRecovery = rte_cpu_to_be_32(tStamp);
	
	struct ipv4_hdr *iph;
	struct udp_hdr *udp;
	iph = (struct ipv4_hdr *)(rte_pktmbuf_mtod(pkt, char *) + sizeof(struct ether_hdr));
	uint16_t ip_hdr_length = (iph->version_ihl & 0x0f)*4;
	udp = (struct udp_hdr *)(rte_pktmbuf_mtod(pkt, char *) + sizeof(struct ether_hdr) + ip_hdr_length); 
	//udp->src_port = htons(NewAddresses[lcore_id].srcPort);
	//udp->dst_port = htons(NewAddresses[lcore_id].dstPort);
	// we are setting these values in makeUdpPacket function
	// delete in future
}
/*
 * calculateTimeStampsForFecPackets(L, D, &created_pkt[index_fec_pkt_buff], columnFEC
 *															dataSymbols);
 */
void calculateTimeStampsForFecPackets( int  L, int D, struct rte_mbuf **fecPacketArray,
										int *columnFEC, struct MarkDataSymbols *dataSymbols)
{
	int row, col, temp;
	uint32_t timeStamp, sumTimeStamps = 0;
	for(col = 0; col<L; col++)
	{
		temp = columnFEC[col];
		for(row = 0; row<D; row++)
		{
			if(dataSymbols[temp].pkt != NULL)
				timeStamp = getTimeStamp(dataSymbols[temp].pkt);
			temp = (temp + L)%65536;
			sumTimeStamps = sumTimeStamps^timeStamp;
		}
		setTimeStamp(sumTimeStamps, fecPacketArray[col]);
		sumTimeStamps = 0;
	}
	
}
uint8_t getProtocol( struct rte_mbuf *pkt )
{
	struct ipv4_hdr *iph;
	iph = (struct ipv4_hdr *)(rte_pktmbuf_mtod(pkt, char *) + sizeof(struct ether_hdr)); 
	return (iph->next_proto_id);	
}
uint32_t getSourceIp( struct rte_mbuf *pkt )
{
	struct ipv4_hdr *iph;
	iph = (struct ipv4_hdr *)(rte_pktmbuf_mtod(pkt, char *) + sizeof(struct ether_hdr)); 
	return (htonl(iph->src_addr));	
}
uint32_t getDestinationIp( struct rte_mbuf *pkt )
{
	struct ipv4_hdr *iph;
	iph = (struct ipv4_hdr *)(rte_pktmbuf_mtod(pkt, char *) + sizeof(struct ether_hdr)); 
	return (htonl(iph->dst_addr));	
}
uint16_t getSourcePort( struct rte_mbuf *pkt )
{
	struct ipv4_hdr *iph;
	struct udp_hdr *udp;
	iph = (struct ipv4_hdr *)(rte_pktmbuf_mtod(pkt, char *) + sizeof(struct ether_hdr));
	uint16_t ip_hdr_length = (iph->version_ihl & 0x0f)*4;
	udp = (struct udp_hdr *)(rte_pktmbuf_mtod(pkt, char *) + sizeof(struct ether_hdr) + ip_hdr_length); 
	return (htons(udp->src_port));	
}
uint16_t getDestinationPort( struct rte_mbuf *pkt )
{
	struct ipv4_hdr *iph;
	struct udp_hdr *udp;
	iph = (struct ipv4_hdr *)(rte_pktmbuf_mtod(pkt, char *) + sizeof(struct ether_hdr));
	uint16_t ip_hdr_length = (iph->version_ihl & 0x0f)*4;
	udp = (struct udp_hdr *)(rte_pktmbuf_mtod(pkt, char *) + sizeof(struct ether_hdr) + ip_hdr_length); 
	return (htons(udp->dst_port));	
}
void setEtherDestination(struct rte_mbuf *pkt)
{
	struct ether_hdr *eth_hdr;
	eth_hdr = rte_pktmbuf_mtod(pkt, struct ether_hdr *);
	ether_addr_copy(&eth_hdr->d_addr, &mc_eth_addr[0]);
}
void makeUdpPacket(struct rte_mbuf *created_pkt)
{
	int lcore_id;
	lcore_id = (int)rte_lcore_id();
	uint8_t *payload;
	uint32_t bond_ip = BOND_IP_1 | (BOND_IP_2 << 8) |
								(BOND_IP_3 << 16) | (BOND_IP_4 << 24);
	struct ether_hdr *eth_hdr;
	struct ipv4_hdr *ip_hdr;
	struct udp_hdr *udp;
	struct rtp_hdr *rtp;
	size_t pkt_size;
	pkt_size = sizeof(struct ether_hdr) + sizeof(struct ipv4_hdr) + sizeof(struct udp_hdr)
																+ sizeof(struct rtp_hdr)
																+ 12    // FEC Header 	
		 														+ 1320; // FEC block

	//printf("pkt_size %d\n", pkt_size);
	created_pkt->data_len = pkt_size;
	created_pkt->pkt_len = pkt_size;
	eth_hdr = rte_pktmbuf_mtod(created_pkt, struct ether_hdr *);
	eth_hdr->ether_type = rte_cpu_to_be_16(ETHER_TYPE_IPv4);
	ether_addr_copy(&ports_eth_addr[0], &eth_hdr->s_addr);
	ether_addr_copy(&mc_eth_addr[0], &eth_hdr->d_addr);
	//print_ethaddr(" dst Address:", &ports_eth_addr[0]);	
	ip_hdr = (struct ipv4_hdr *)(rte_pktmbuf_mtod(created_pkt, char *) + sizeof(struct ether_hdr));
	ip_hdr->version_ihl = 0x45;
	ip_hdr->type_of_service = 0xc0;
	ip_hdr->total_length = htons(pkt_size-sizeof(struct ether_hdr));    // doubt
	ip_hdr->packet_id = 1;
	ip_hdr->fragment_offset = htons(0x4000);
	ip_hdr->time_to_live = 19;
	ip_hdr->next_proto_id = 17;
	ip_hdr->hdr_checksum  =  0;
	//ip_hdr->src_addr = htonl(parseIPV4string("172.16.1.2"));	//	htonl(sourceIp);     
	//ip_hdr->dst_addr = htonl(parseIPV4string("232.100.1.1"));	// 	htonl(multiCastIp);  
	ip_hdr->src_addr = NewAddresses[lcore_id].sourceAdd;
	ip_hdr->dst_addr = NewAddresses[lcore_id].groupAdd;
	ip_hdr->hdr_checksum = rte_ipv4_cksum(ip_hdr);	
	udp = (struct udp_hdr *)(rte_pktmbuf_mtod(created_pkt, char *) 
							+ sizeof(struct ether_hdr) 
							+ sizeof(struct ipv4_hdr));
	udp->src_port    =  (NewAddresses[lcore_id].srcPort);      // htons() is done before;
    udp->dst_port    =  htons(htons(NewAddresses[lcore_id].dstPort) + 2); 
    udp->dgram_len   =  htons(sizeof(struct udp_hdr) + sizeof(struct rtp_hdr) + 12 + 1320 );
    udp->dgram_cksum =  0;
	rtp = (struct rtp_hdr *)(rte_pktmbuf_mtod(created_pkt, char *) 
							+ sizeof(struct ether_hdr) 
							+ sizeof(struct ipv4_hdr)
							+ sizeof(struct udp_hdr));
	
	rtp->synSource =  htonl(0x12345678);
	//rtp->conSource =  htonl(0x12345678);
	rtp->seqNumber =  htons(49059);
	rtp->timeStamp =  htonl(33333);
	rtp->payloadT = (96); 
	rtp->ver = 2;
	rtp->cc = 0;
	rtp->marker = 0;
	//udp->dgram_cksum =  rte_ipv4_cksum(ip_hdr);
}

// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
// %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



// Demonstration of how to use the C interface.
// This is kinda basic, we use only one function
// to encode, drop some (random) packets, and then
// decode what remains.

// Encode / decode "mysize" uint32_t
// for a more elaborate examlpe with different alignments, see test_cpp
void symbolWriteToPacket(struct rte_mbuf *pkt_arr, uint32_t dataLength, uint32_t *ptr, uint32_t ID, uint16_t seqNumber );
bool decode (uint32_t mysize, float drop_prob, uint8_t overhead, struct rte_mbuf **pkt_arr);
void symbolWriteToPacket(struct rte_mbuf *pkt, uint32_t dataLength, uint32_t *copyFrom, uint32_t ID, uint16_t seqNumber )
{
	uint32_t *payload;
	struct fec_hdr *fec;
	
	payload = (uint32_t *)(rte_pktmbuf_mtod(pkt, char *)
							+ sizeof(struct ether_hdr)
							+ sizeof(struct ipv4_hdr)
							+ sizeof(struct udp_hdr)
							+ sizeof(struct rtp_hdr)
							+ sizeof(struct fec_hdr));
	
	fec = (struct fec_hdr *)(rte_pktmbuf_mtod(pkt, char *)
							+ sizeof(struct ether_hdr)
							+ sizeof(struct ipv4_hdr)
							+ sizeof(struct udp_hdr)
							+ sizeof(struct rtp_hdr));
	fec->sequenceNumberBase = rte_cpu_to_be_16(seqNumber);
	fec->M = L;  // M, L for columns
	fec->N = D;  // N, D for rows
	
	//rtp->payloadT = 33;  // 96 decimal
	//*payload = ID;
	//payload++;
	
	if(memcpy(payload, copyFrom, dataLength*4) == NULL )
	{
		printf("Fail To memcpy symbol into Packet\n ");
	}
}
int sendPacketQ(struct rte_mbuf **mbuf, int port)
{
	int ret;
	unsigned lcore_id;
	lcore_id = rte_lcore_id();
	do{
	ret = rte_ring_sp_enqueue(lcore_para[lcore_id].worker_tx, (void *)mbuf[0]);
	}while(ret==-ENOBUFS);

	if(ret!=0)
	{
		lcore_para[lcore_id].missed_tx +=1;
	}
	return ret;
}

int linearizeSending(struct rte_mbuf **data_pkt, struct rte_mbuf **created_pkt, int L, int D,
					struct MarkDataSymbols *dataSymbols, int *columnFec, int totalSymbols)
{
	unsigned lcore_id;
	lcore_id = rte_lcore_id();
	int dataCount, fecCount = 0, ret, temp = 1, x, y, sym;
	bool skip = false;
	uint16_t seqBase, seq;
	for(x = 0; x<L; x++)
	{
		sym = columnFec[x];
		if(sym == -1)
			continue;
		for(y = 0; y<D; y++)
		{
			if(dataSymbols[sym].Mark != true)
				columnFec[x] = -1;
			sym = (sym + L)%65536;
		}
	}
	int drop = (rand()%23);
	drop = 100;
	for(dataCount = 1; dataCount <= totalSymbols; dataCount++ )   // starting from 1
	{
		seq = getSequenceNumber((const u_char**)&data_pkt[dataCount-1]->buf_addr);
		//printf("\t\t\t\t%d\n", seq);
		if(dataSymbols[seq].Mark != true)
			continue;
		if( (dataCount-1) == drop )
		{
			//seq = getSequenceNumber((const u_char**)&data_pkt[dataCount-1]->buf_addr);
			//printf("PACKET LOST: %d\n", seq);
			skip = true;
		}
		if(!skip)
		{
			c_count--;
			insertVlanTag(data_pkt[dataCount-1]);
			
			ret = sendPacketQ(&data_pkt[dataCount-1], 0);
			//printf("------DATA SYmbol-------------ret %d\n", ret);
			//while(1);
		}
		else
		{
			rte_pktmbuf_free(data_pkt[dataCount-1]);
		}
		if(dataCount == 1 || dataCount == temp)
		{
			seqBase = getSequenceNumberBase(created_pkt[fecCount]);
			if( (seqBase == -1) || (columnFec[fecCount] == -1) )
			{
				rte_pktmbuf_free(created_pkt[fecCount]);
				fec_leaving--;
			}
			else 
			{
				insertVlanTag(created_pkt[fecCount]);
				ret = sendPacketQ(&created_pkt[fecCount], 0);
				//printf("------FEC SYmbol-------------ret %d\n", ret);
			//	if(ret==1)
					fec_leaving--;
			}
			//printf("packet sent %d\n", ret );
			temp = (temp + D)%65536;
			//rte_pktmbuf_free(created_pkt[fecCount]);
			fecCount++;
		}
		skip = false;
		dataSymbols[seq].Mark = false;
		dataSymbols[seq].pkt  = NULL;
	}
return 0;
}
//#############################################################//
int generateRepairSymbols(int colums,int rows, uint32_t *buffer, struct rte_mbuf **pkt_arr, int *seqArray)
{
	int D = 0;
	uint32_t packetCount = 0, bogusId = 0;
	struct pair 
	{
		uint32_t id;
		uint32_t *symbol;
	};
	struct RaptorQ_ptr *enc[colums];
	// will keep "sent" symbols here.
	struct pair encoded[colums];
	// symbol and sub-symbol sizes
	const uint16_t subsymbol = 64;
	const uint16_t symbol_size = 1320;  // should be taken as 330x4 = 1320
	int delay1 = 999999, delay2 = 999999;
	
	/*
	 * Now start decoding things
	 */
	// use multiple blocks
		// ref
		//struct RaptorQ_ptr *enc = RaptorQ_Enc (ENC_32, myvec, mysize, subsymbol,
		//													symbol_size, 200);
		// myvec = 128 x 4
		// mysize = 128
		// ref
	for(int L=0; L<colums; L++)
	{
		
		// making space for each repair symbol
		encoded[L].symbol = (uint32_t *) malloc (symbol_size);
		enc[L] = RaptorQ_Enc (ENC_32, &buffer[D*330], 330*rows, subsymbol, symbol_size, 1320*rows);
		// D*1320 ?
		// 330x4 = 1 packet, so Dx1320 = 4 packets in column
		
		if (enc[L] == NULL) {
			fprintf(stderr, "Could not initialize encoder.\n");
			return false;
		}
		
		D = D + rows;  // 4 corresponds to the row i-e 6x4
		// start background precomputation while we get the source symbols.
		RaptorQ_precompute (enc[L], 2, true);	
		
	}
	//printf("-----------------------------------------------------------\n");
	uint32_t symbols_tot = 0, overhead = 1;
	for (uint8_t b = 0; b < RaptorQ_blocks (enc[0]); ++b) {
		uint16_t sym = RaptorQ_symbols (enc[0], b);
		symbols_tot += (sym + overhead);
		//printf("Block: %i, Symbol: %d, overhead: %d\n", b, sym, overhead);
	}
	/*
	printf("Total Symbols: %d\n", symbols_tot);
	printf("Total blocks for enc[0]: %d\n", RaptorQ_blocks (enc[0]));
	printf("Total blocks for enc[1]: %d\n", RaptorQ_blocks (enc[1]));
	printf("Total blocks for enc[2]: %d\n", RaptorQ_blocks (enc[2]));
	printf("-----------------------------------------------------------\n");
	*/
	for(int L=0; L<colums; L++)
	{
		uint32_t data_size;
		data_size = symbol_size/sizeof(uint32_t);
		uint32_t *data = encoded[L].symbol;
		uint64_t written = RaptorQ_encode (enc[L], (void **)&data, data_size, rows, 0 ); 
		//sleep(1);
		//printf("Encoder: %d %llu\n",L, written);
		// ... 0, 0 should be replaced, if we desire more then 1 repair symbol per column
		symbolWriteToPacket(pkt_arr[packetCount], data_size, encoded[L].symbol, 3, seqArray[L]);
		//printf("after symbolWriteToPacket\n");
		// bogusId can be effectively replaced with sequence number of 
		// first column Packet. TO identify repair sym belongs to which source pkts.
		packetCount++;
		bogusId++;
		delay1 = 99999999;
		delay2 = 99999999;
		free(encoded[L].symbol);
		
	}
//	printf("Repair Symbols : %d\n", packetCount );
	for(int L=0; L<colums; L++)
	{
		uint32_t oti_scheme = RaptorQ_OTI_Scheme (enc[L]);
		uint64_t oti_common = RaptorQ_OTI_Common (enc[L]);
		//printf("encoder data: %d\n", L+1);
		//rintf("----> oti_scheme: %d,  oti_common = %llu\n", oti_scheme, oti_common);
		RaptorQ_free(&enc[L]);
		
	}
	//while(1);
	return 0;


}
void dispBytes(uint32_t* buffer1, int startBuffer)
{
	uint8_t *temp;
	temp = (uint8_t *)&buffer1[( (startBuffer-1) * 330 )];
	for(int x = 0; x<10; x++)
	{
		printf("%x ",temp[x]);
		if(x%16 == 0)
			printf("\n");
	}
	printf("\n");
}
bool packetMbufsFec(struct rte_mbuf **fec_pkt,  int fec_length)
{
	int count;
	for(count = 0; count < fec_length; count++)
	{
		
			fec_pkt[count] = rte_pktmbuf_alloc(pktmbuf_pool[0]);
			if( (fec_pkt[count] == NULL) ) 
			{
				rte_exit(EXIT_FAILURE,
						"Cannot allocate mbuf for fec packet %d\n", 0);
			}
			makeUdpPacket(fec_pkt[count]);
	}
	return true;
}
bool packetMbufsSource(struct rte_mbuf **data_pkt, int dataPkt_length)
{
	//printf("A ");
	int count;
	for(count = 0; count < dataPkt_length; count++)
	{
		data_pkt[count] = rte_pktmbuf_alloc(pktmbuf_pool[0]);
		if ( (data_pkt[count] == NULL) ) 
		{
			rte_exit(EXIT_FAILURE,
						"Cannot allocate mbufs for data packet %d\n", 0);
		}
	}		   
	return true;
}	


//#############################################################//
int lcore_hello( void )
{
	// Encoder main processing loop
	//int L, D;   // L columns, D rows
	//L = 6;
	//D = 4;
	if(L <= 0 || D <= 0)
		rte_exit(EXIT_FAILURE, "L & D must be initialized properly...\n");
	int lcore_id;
	lcore_id = (int)rte_lcore_id();
	printf("hello from lcore_hello %u, L = %d, D = %d\n", lcore_id, L, D);
	uint8_t type;
	struct MarkDataSymbols dataSymbols[65536];
	int fec_length;
	fec_length     = 500;
	fec_length     = fec_length - (fec_length%L);     // making it multiple of L
	struct rte_mbuf *created_pkt[fec_length];         // used for sending fec  packets
	struct rte_mbuf *data_pkt[MAX_PKT_BURST];         // used for sending data packets
	struct rte_mbuf *data_pkt_array[500];              // only holds addresses of mbuf's, those need to 
	struct rte_mbuf *dup_pkt_array[500];               // sent with repair symbols
	printf("fec_length = %d\n", fec_length);
	if(!packetMbufsFec(created_pkt, fec_length))
	{
		//printf("%u\n", rte_mempool_get_count(pktmbuf_pool[0]));
		printf("Mbufs not Alslocated: fec\n");
		exit(1);
	}
						
	size_t total_mem_buffer;
	total_mem_buffer = L*D*1320;
	uint32_t *bufferArray[2], *tbuffer1;
	uint32_t *buffer1 = (uint32_t *) malloc (total_mem_buffer); // L*D*1320
	
	uint32_t *buffer2 = (uint32_t *) malloc (total_mem_buffer); // L*D*1320
	if(buffer1 == NULL)
	{
		printf("please check memory: not enough memory \n");
		exit(1);
	}
	bufferArray[0] = buffer1;
	bufferArray[1] = buffer2;
	for(int k = 0; k < 65536; k++)
	{
		dataSymbols[k].Mark = false;
		dataSymbols[k].pkt = NULL;
	}
	int index_fec_pkt_buff = 0; 
	int columnFEC[30]; // should be L
	for(int k=0; k<30; k++)
		columnFEC[k]=-1;
	int indexFecSequence = 0;
	struct rte_mbuf * m;
	int packet_count = 0;
	void *pkt;
	// Allocating LxDx1320 byte buffer to accomudate LxD symbols at a time
	// 1320 = 330x4, packet lengths are 1374-54 (header ETH_IP_UDP_RTP = 54)
	int numPackets = 0,  e_count=0;
	bool exitFromLoop = true;
	bool includeInEncoder = false, timerSet = false;
	uint16_t pivot = 0, diff = 0, nextBlock = 0;
	while(!force_quit)
	{
		const uint8_t *offset;
		uint16_t seq;
		uint8_t type;
		int startBuffer = 0;
		bool Read = true;
		int totalSym = 0,  xret =0, row = 0, col = 0, sym = 0, blocks_count = 0, indx=0;
		void *pkts[64];
		while(!force_quit)
		{ 
			
			//numPackets = rte_eth_rx_burst(0, 0, data_pkt, MAX_PKT_BURST);
			if(lcore_para[lcore_id].worker_rx != NULL)
				numPackets = rte_ring_sc_dequeue_burst(lcore_para[lcore_id].worker_rx, pkts,32, NULL);
			
			if(numPackets)
			{
				//printStats();
				for(int k = 0; k<numPackets; k++)
				{
					data_pkt[k] = (struct rte_mbuf *)pkts[k];
					assignNewIpSourceGroup(data_pkt[k], (int)lcore_id);
					if(NewAddresses[lcore_id].set != true)
					{
						/*
						NewAddresses[lcore_id].sourceAdd = getSourceIp(pktarr[x]);
						NewAddresses[lcore_id].groupAdd = getDestinationIp(pktarr[x]);
						NewAddresses[lcore_id].srcPort = getSourcePort(data_pkt[k]);
						NewAddresses[lcore_id].dstPort = getDestinationPort(data_pkt[k])+2;
						NewAddresses[lcore_id].set = true;
						packetMbufsFec(created_pkt, fec_length); // Required to call here only once for first block fec
						*/
						
						/*
						 * above block might be needed, if we are not modify orignal (s,g)
						*/
					}
					//printf("Packets received \n");
					//rte_pktmbuf_free(data_pkt[k]);
				}
				//numPackets = 0;
			}
			rte_timer_manage();
			if(numPackets)
			{ //xtra 1
				rte_timer_manage();
					c_count= c_count+numPackets;
				//printf("%d %d  %d %d %d\n", c_count, notSent, e_count, totalSym, fec_leaving);
				for(int x = 0; x < numPackets; x++)
				{ // xtra 2
					//rte_vlan_strip(data_pkt[x]);
					//type = packetType(data_pkt[x]);     // 0 = rtp, 1 = fec, 2 = other
					//printf("type = %d\n", type);
					//rte_vlan_strip(data_pkt[x]);
					//	if(blocks_count%101 == 0)	
					//		printf("-Blocks sent: %d\n", blocks_count);
					uint32_t destIp = getDestinationIp(data_pkt[x]);
					type = packetType(data_pkt[x]);     // 0 = rtp, 1 = fec, 2 = other
					//printf("destIp = %x, type = %d, multiCastIp = %x\n", destIp, type, multiCastIp);
					//printf("%d %d %d\n", destIp==multiCastIp, type!=FEC, type != OTHER);
					// 225.53.6.13
					// (destIp == multiCastIp) &&
					if( (type != FEC) && (type != OTHER))
					{ // xtra 3
						seq = getSequenceNumber((const u_char**)&data_pkt[x]->buf_addr);
					//	printf("[ seq = %d ] ", seq);
						sourceIp    = getSourceIp(data_pkt[x]);
						setEtherDestination(data_pkt[x]);
						data_pkt_array[totalSym++] = data_pkt[x];
						dataSymbols[seq].Mark = true;
						dataSymbols[seq].pkt  = data_pkt[x];
						if(totalSym >= (L*D))
							includeInEncoder = true;
					}
					else
					{
						rte_pktmbuf_free(data_pkt[x]);
						c_count--;//printf("# # # mbuf_free\n");
					}
				}
				if(includeInEncoder)
				{
					e_count= e_count+1;
					if(blocks_count%2 == 0)
						tbuffer1 = bufferArray[0];
					else
						tbuffer1 = bufferArray[1];
					int ind, encTotalSym = 0,
					col = 0;
					row = 0;
					for(ind = 0; ind < totalSym; ind++)
					{	
						rte_timer_manage();
						//printf("\t\t\tdeInEncoder type: %d\n", type);
						seq = getSequenceNumber((const u_char**)&data_pkt_array[ind]->buf_addr);
						//printf("# e-seq = %d\n", seq);
						offset = (uint8_t*) rte_pktmbuf_mtod( data_pkt_array[ind], char *) + 54;
						startBuffer = 1 + row + (col*D);
						//printf("startBuffer %d, col %d\n", startBuffer, col);
						rte_memcpy ( (uint32_t*) &tbuffer1[ (startBuffer-1)*330], offset, 330*4);  // startBuffer-1, adjusting for 0
						if(col < L && row == 0)
						{
							//columnFEC[indexFecSequence++] = seq;
							columnFEC[col] = seq;
							//printf("\t\t\t[->]FEC sequence Base: %d\n", seq);
							// these packets are Dx330x4 bytes apart in buffer!
						}
						col++;  // its location is challenging
						if((dataSymbols[((seq+1)%65536)].Mark != true) && (encTotalSym < (L*D-1)))
						{
							col++;
							encTotalSym++;
							//printf("GOT TRUE\n");
						}
						if( col > (L-1) ) 
						{
							col = 0;
							row++;
						}
						encTotalSym++;
						if( encTotalSym >= (L*D) )
							break;	
					}
					//printf("encTotalSym = %d, ind = %d\n", encTotalSym, ind);
					for(int x = ind+1; x<totalSym; x++)
						dup_pkt_array[indx++] = data_pkt_array[x];
					totalSym = totalSym - indx;
					//startBuffer = col*D+1+row;
					indexFecSequence = 0;
					// Now LxD memory buffer is filled with symbols (packets), start encoding, generate 
					// repair symbols for each column
					
					int n = generateRepairSymbols(L, D, tbuffer1, &created_pkt[index_fec_pkt_buff], columnFEC);
					
					calculateTimeStampsForFecPackets(L, D, &created_pkt[index_fec_pkt_buff], 
															 columnFEC, dataSymbols);
					
					notSent++;
					n = linearizeSending(&data_pkt_array[0], &created_pkt[index_fec_pkt_buff], L, D, 
												dataSymbols, columnFEC, totalSym);
					//printf("total 1 block sent\n");
					lcore_para[lcore_id].blocks +=1;	
					notSent--;
					totalSym = 0;
					col = 0;
					row = 0;
					sym = 0;
					index_fec_pkt_buff  = index_fec_pkt_buff  + L;
					//printf("[+]index_data_pkt_buff: %d, dataPkt_length: %d\n", index_data_pkt_buff, dataPkt_length);
					//blocks_count++;
					if( index_fec_pkt_buff>= (fec_length-100))
					{	
						index_fec_pkt_buff -= L;
						//printf("ifpb %d\n", index_fec_pkt_buff);
						int fr;
						for(fr = index_fec_pkt_buff; fr<fec_length; fr++)
						{
							rte_pktmbuf_free(created_pkt[fr]);
							fec_leaving--;
						}
						index_fec_pkt_buff  = 0;
						if(!packetMbufsFec(created_pkt, fec_length))
						{
							//printf("%u\n", rte_mempool_get_count(pktmbuf_pool[0]));
							printf("Mbufs not Alslocated: fec\n");
							exit(1);
						}
						fec_leaving = fec_leaving +fec_length;
					}
					for(int k=0; k<L; k++)
						columnFEC[k] = -1; 
					for(int x = 0; x<indx; x++)
					{
						data_pkt_array[x] = dup_pkt_array[x];
						totalSym++;
					}
					indx = 0;
					if(BLOCKS != 0 )
					{
						if(lcore_para[lcore_id].blocks == BLOCKS)
						{
							force_quit = true;
						}
						
					}
					blocks_count++; // buffer shuffle is hapening on this var: proper removal required
				}  // includeInEncoder
					includeInEncoder = false;
			}  // for: var x
		}
	}
	return 0;
}
static int
main_processing_loop(__attribute__((unused)) void *arg)
{
	int ret;
	unsigned lcore_id;
	lcore_id = rte_lcore_id();
	printf("main_processing_loop launched %u\n", lcore_id);
	if(lcore_id == 0)
	{
		lcore_Distributer();
	}
	else if(lcore_id == 1)
	{
		lcore_IGMP();
	}
	else if(lcore_id == 2)
	{
		lcore_TX();
	}
	else if (lcore_id >= 3)
	{
		lcore_hello();
	}
}
static void
signal_handler(int signum)
{
	if (signum == SIGINT || signum == SIGTERM) {
		printf("\n\nSignal %d received, preparing to exit...\n",signum);
		force_quit = true;
		
		#ifdef RTE_LIBRTE_PDUMP
			rte_pdump_uninit();
		#endif
		
	}
}

int
main(int argc, char **argv)
{
	#ifdef RTE_LIBRTE_PDUMP
		rte_pdump_init(NULL);
	#endif
	force_quit = false;
	signal(SIGINT, signal_handler);
	signal(SIGTERM, signal_handler);
	int ret, socketid = 0;
	unsigned lcore_id;
	struct rte_eth_conf port_conf;
	memset(&port_conf,0,sizeof(rte_eth_conf));
	port_conf.rxmode.split_hdr_size = 0;
	port_conf.rxmode.header_split = 0;
	port_conf.rxmode.hw_ip_checksum = 1;
	port_conf.rxmode.hw_vlan_filter = 0;
	//port_conf.rxmode.ignore_offload_bitfield = 1,
	//port_conf.rxmode.offloads = DEV_RX_OFFLOAD_CHECKSUM;
	//port_conf.txmode.hw_vlan_insert_pvid=0;
	port_conf.rxmode.jumbo_frame = 0;
	port_conf.rxmode.hw_strip_crc = 0;
	port_conf.rxmode.mq_mode = ETH_MQ_RX_NONE;
	port_conf.rx_adv_conf.rss_conf.rss_key = NULL,
	port_conf.rx_adv_conf.rss_conf.rss_hf  = ETH_RSS_IP,
	//port_conf.txmode.mq_mode = ETH_MQ_TX_DCB;//ETH_MQ_TX_NONE,
	ret = rte_eal_init(argc, argv);
	if (ret < 0)
		rte_panic("Cannot init EAL\n");
	argc -= ret;
	argv += ret;
	ret = parse_args(argc, argv);
	if(ret < 0)
		rte_exit(EXIT_FAILURE, "parse arguments correctly\n");
	/* init memory */
	ret = init_mem(NB_MBUF);
	if(ret < 0)
		rte_exit(EXIT_FAILURE, "init_mem faild\n");
	/* Hash Setup */
	setup_hash(0);
	printf("RR\n");
	//sleep(1);
	//int ports = 2;
	for(int x = 0; x<ports; x++)
	{
		ret = rte_eth_dev_configure(x, 1, 1, &port_conf);
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "Cannot configure device: err = ?, port = ?\n");
			ret = rte_eth_tx_queue_setup(x, 0, nb_txd, socketid, NULL);
			//ret = rte_eth_tx_queue_setup(x, 1, nb_txd, socketid, NULL);
		if(ret == -ENOMEM)
			printf("\nunable to allocate the tx ring descriptors");
		else if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_tx_queue_setup: err = ? port = ?\n");
		ret = rte_eth_rx_queue_setup(x, 0, nb_rxd, socketid, NULL, pktmbuf_pool[0]);
		if(ret == -ENOMEM)
			printf("\nunable to allocate the rx ring descriptors");
		else if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_rx_queue_setup: err = ? port = ?\n");
		rte_eth_promiscuous_enable( x);
		/* Start device */
		ret = rte_eth_dev_start(x );
		if (ret < 0)
			rte_exit(EXIT_FAILURE, "rte_eth_dev_start: err = ?, port = ?\n");
	}
	rte_eth_macaddr_get(0, &ports_eth_addr[0]);     // portId , portId
	print_ethaddr(" src Address:%s", &ports_eth_addr[0]);
	printf("\n");
	printf("Total DPDK devices %d\n", rte_eth_dev_count());
	/* call lcore_hello() on every slave lcore */
	RTE_LCORE_FOREACH_SLAVE(lcore_id) {
		rte_eal_remote_launch(main_processing_loop, NULL, lcore_id);
	}

	/* call it on master lcore too */
	main_processing_loop(NULL);

	rte_eal_mp_wait_lcore();
	return 0;
}
