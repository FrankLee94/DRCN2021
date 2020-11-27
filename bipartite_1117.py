# !usr/bin/env python
# -*- coding:utf-8 -*-

# this model is for compare between variance and vector distance
# Jialong Li 2020/11/15


import networkx as nx
from networkx.algorithms import bipartite
import xlrd
import copy
import random
import math
import pandas as pd
from itertools import islice


class Embedding:
	def __init__(self):
		self.FG_NUM = 1000			# 业务数
		self.VNF_LIST = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J']		# 10个网络功能
		self.VNF_min = 2			# 一条链最少2个VNF
		self.VNF_max = 6			# 一条链最多6个VNF
		self.BD_min = 1				# 业务请求最小带宽1G
		self.BD_max = 10			# 业务请求最大带宽10G
		self.CPU_min = 1			# 对于单个VNF,CPU最小请求1
		self.CPU_max = 10			# 对于单个VNF,CPU最大请求10
		self.RAM_min = 1			# 对于单个VNF,CPU最小请求1
		self.RAM_max = 10			# 对于单个VNF,CPU最大请求10		
		self.CPU_CAPA = 100			# 单节点CPU容量
		self.RAM_CAPA = 100			# 单节点RAM容量
		self.WAVE_NUM = 10			# 链路波长数
		self.WAVE_CAPA = 100		# 单波长100G		
		self.node_load = {}			# 节点总负载
		self.edge_load = {}			# 边的总负载
		self.wave_load = {}			# 波长负载
		self.vm_idx = {}			# 每个FG接入具体节点，使用的链路
		self.lp_idx = {}			# 一跳光路索引
		self.arr_rate = 100			# 到达率100
		self.ser_rate = 10			# 服务率10，业务平均持续时间1/10, 100ms
		self.KSP = 5				# ksp算法中的K条路径
		self.G_topo = None			# 物理拓扑
		self.NODE_NUM = 24			# 拓扑节点数量
		# self.traff_df = None		# 储存一次模拟的业务信息
		self.traff_df = pd.read_excel('./traffic.xlsx')
		self.INF = 99999999			# 无穷大
		self.topo_file_p = './topology/topo_usnet.xlsx'

	# 从xlsx文件里面读取拓扑数据。
	def read_topo_file(self):
		G_topo = nx.Graph()
		workbook = xlrd.open_workbook(self.topo_file_p)
		booksheet = workbook.sheet_by_index(0)		# 读取第一页的全部内容
		nrows = booksheet.nrows						# 一共有多少行数据
		for i in range(1, nrows):					# 第0行不要
			row = booksheet.row_values(i)			# 每一行里面的数据
			for j in range(1, nrows):				# 第0列不要
				if i == j:							# 避免出现环
					continue
				else:
					if int(row[j]) != 0:			# 有边
						G_topo.add_edge(i-1, j-1, weight = int(row[j]))
					else:
						continue		# 无边
		self.G_topo = G_topo

	# 产生泊松流，单位是μs
	def traff_gene(self):
		pro_poisson = random.random()
		if pro_poisson == 0.0 or pro_poisson == 1.0:
			pro_poisson = 0.5
		intval = -(1e6 / self.arr_rate) * math.log(1 - pro_poisson)			# event intval
		intval = int(round(intval))
		pro_poisson = random.random()
		pers_time = -(1e6 / self.ser_rate) * math.log(1 - pro_poisson)		# event service time
		pers_time = int(round(pers_time))
		if intval == 0:			# 避免出现两个业务间隔时间为0的情况
			intval = 1
		if pers_time == 0:		# 避免出现某个业务持续时间为0的情况
			pers_time = 1
		return intval, pers_time

	# 虚拟网络功能产生
	def vnf_gene(self):
		VNF_dict = {}
		VNF_order = []
		vnf_num = random.randint(self.VNF_min, self.VNF_max)		# VNF数量，包前包后
		for vnf in random.sample(self.VNF_LIST, vnf_num):
			cpu = random.randint(self.CPU_min, self.CPU_max)
			ram = random.randint(self.RAM_min, self.RAM_max)
			VNF_dict[vnf] = [cpu, ram]		# 构建一条链
			VNF_order.append(vnf)
		bd = random.randint(self.BD_min, self.BD_max)
		s = random.randint(0, self.NODE_NUM - 1)		# 请求源节点
		d = random.randint(0, self.NODE_NUM - 1)		# 请求宿节点
		return s, d, bd, VNF_dict, VNF_order

	# 对产生的业务进行排序
	def traff_sort(self):
		traff_info = {'req_no': [], 'timing': [], 'pers_time':[], 's': [], 'd': [], 
					'bd': [], 'vnf_num': [], 'vnf': [], 'vnf_order':[], 'status': []}
		abs_time = 0
		for i in range(self.FG_NUM):
			intval, pers_time = self.traff_gene()
			s, d, bd, VNF_dict, VNF_order = self.vnf_gene()
			abs_time += intval
			arriv_time = abs_time
			leave_time = arriv_time + pers_time
			for j in range(2):			# 一个请求分为到达和离开两阶段
				traff_info['req_no'].append(i)
				traff_info['s'].append(s)
				traff_info['d'].append(d)
				traff_info['bd'].append(bd)
				traff_info['vnf_num'].append(len(VNF_dict))
				traff_info['vnf'].append(copy.deepcopy(VNF_dict))
				traff_info['vnf_order'].append(copy.deepcopy(VNF_order))
				traff_info['pers_time'].append(pers_time)
			traff_info['timing'].append(arriv_time)
			traff_info['timing'].append(leave_time)
			traff_info['status'].append('arriv')
			traff_info['status'].append('leave')
		df = pd.DataFrame(traff_info)
		self.traff_df = df.sort_values(by='timing', axis=0, ascending=True)
		# print(self.traff_df)

	# Ksp算法
	def k_shortest_paths(self, s, d, weight=None):
		return list(islice(nx.shortest_simple_paths(self.G_topo, s, d, weight=weight), self.KSP))

	# 拓扑初始化
	# node_load = {}
	# edge_load = {}
	# vm_idx = {}
	# lp_idx：key为源宿节点组成的元组,value是dict，里面包含多个lp的信息，每个lp是一个list
	# lp_idx：double dict结构 {(1,2):{id:lp, id:lp}, (2,3):{id:lp, id:lp}}
	# wave_use_idx = {}
	def topo_init(self):
		for edge in [e for e in self.G_topo.edges]:
			self.edge_load[edge] = 0
			self.edge_load[(edge[1], edge[0])] = 0		# 双向链路
			self.wave_load[(edge)] = [0 for i in range(self.WAVE_NUM)]
			self.wave_load[(edge[1], edge[0])] = [0 for i in range(self.WAVE_NUM)]
		for node in [n for n in self.G_topo.nodes]:
			self.node_load[node] = [0, 0]		# 0表示CPU, 1表示RAM
		self.vm_idx = {}
		self.lp_idx = {}

	# 业务接入，节点负载增加
	def fill_node_load(self, row):
		req_no = int(row['req_no'])
		match = self.vm_idx[req_no][1]
		# row['vnf'] key为虚拟网络功能，value为需要的cpu
		for key, value in eval(row['vnf']).items():
			map_node = match[key]		# 得到虚拟网络功能对应的节点
			self.node_load[map_node] += value

	# 业务离开，节点负载减少
	def rele_node_load(self, row):
		req_no = int(row['req_no'])
		match = self.vm_idx[req_no][1]
		# row['vnf'] key为虚拟网络功能，value为需要的cpu
		for key, value in eval(row['vnf']).items():
			map_node = match[key]		# 得到虚拟网络功能对应的节点
			self.node_load[map_node] -= value

	# 业务接入，链路负载增加
	def fill_edge_load(self, row):
		bd = int(row['bd'])
		req_no = int(row['req_no'])
		all_best_paths = self.vm_idx[req_no][2]
		for path in all_best_paths:
			for i in range(len(path) - 1):
				s = path[i]
				d = path[i+1]
				self.edge_load[(s, d)] += bd

	# 业务离开，链路负载减少
	def rele_edge_load(self, row):
		bd = int(row['bd'])
		req_no = int(row['req_no'])
		all_best_paths = self.vm_idx[req_no][2]
		for path in all_best_paths:
			for i in range(len(path) - 1):
				s = path[i]
				d = path[i+1]
				self.edge_load[(s, d)] -= bd

	# 寻找节点映射，二部图方法
	# 得到的最优匹配，是一个dict,如：{0: 'A', 1: 'B', 'A': 0, 'B': 1}
	# eval，把字符串的dict转为dict
	# 只采用CPU的容量
	def bip_find_node(self, row):
		G = nx.Graph()
		G.add_nodes_from([n for n in self.G_topo.nodes], bipartite=0)
		G.add_nodes_from([n for n in eval(row['vnf']).keys()], bipartite=1)
		for node_top in [n for n in self.G_topo.nodes]:
			for node_down in eval(row['vnf']).keys():
				w = eval(row['vnf'])[node_down][0] - (self.CPU_CAPA - self.node_load[node_top])
				if w > 0:
					w = self.INF		# 此时节点cpu容量无法布置该网络功能
					G.add_edge(node_top, node_down, weight=w)
				else:
					G.add_edge(node_top, node_down, weight=w)
		# 这里构建的二部图是完全二部图，所选节点是否可行后续需要验证
		return bipartite.matching.minimum_weight_full_matching(G, weight='weight')

	# 判断二部图找到的节点是否可行
	def bip_judge_node(self, matcth, row):
		is_node = True
		for node_down in eval(row['vnf']).keys():
			map_node = matcth[node_down]		# 这是映射到的物理节点
			w = eval(row['vnf'])[node_down][0] - (self.CPU_CAPA - self.node_load[map_node])
			if w > 0:		# 此时节点cpu容量无法布置该网络功能
				is_node = False
				return is_node
			else:
				pass
		return is_node

	# 判断k条最短路中的一条是否可用，并返回每段链路中的剩余带宽最大值，使用的波长号
	def bip_judge_path(self, row, path):
		is_path = False
		wave = -1

		# 先判断已有光路是否可行
		s = path[0]
		d = path[-1]
		if (s, d) in self.lp_idx.keys():		# 已有一跳的光路
			for lp_id, lp in self.lp_idx[(s, d)].items():
				if lp[4] + int(row['bd']) <= self.WAVE_CAPA:		# 资源符合
					wave = lp[3]
					is_path = True
					break
		else:									# 看是否可以新建光路
			for wv in range(self.WAVE_NUM):		# 逐条波长检查
				Flag = True
				for i in range(len(path) - 1):
					s = path[i]
					d = path[i+1]
					if self.wave_load[(s, d)][wv] > 0:		# 波长已用
						flag = False
						break
				if flag:
					wave = wv
					is_path = True
					break

		min_bd = self.INF
		for i in range(len(path) - 1):
			s = path[i]
			d = path[i+1]
			if self.edge_load[(s, d)] < min_bd:
				min_bd = self.edge_load[(s, d)]
		return is_path, wave, min_bd

	# k条最短路径里面找一条，包含最大剩余带宽的
	def bip_find_best_path(self, row, k_paths):
		all_min_bd = self.INF
		best_path = []
		for path in k_paths:
			is_path, min_bd = self.bip_judge_path(row, path)
			if is_path:		# 该链路是可行的，找包含最大剩余带宽的
				if min_bd < all_min_bd:
					best_path = path
					all_min_bd = min_bd
			else:
				pass
		return best_path

	# 寻找每两个功能之间的单条可用链路
	def bip_find_paths(self, row, match):
		all_best_paths = []
		for i in range(0, int(row['vnf_num']) + 1):
			if i == 0:						# 源节点到第一个网络功能
				s = int(row['s'])
				d_vnf = eval(row['vnf_order'])[0]		# 物理功能宿节点
				d = match[d_vnf]						# 映射的具体节点
				if s == d:		# 第一个功能部署在源节点
					all_best_paths.append(copy.deepcopy([]))
					continue
			elif i == int(row['vnf_num']):	# 最后网络功能到宿节点
				d = int(row['d'])
				s_vnf = eval(row['vnf_order'])[i-1]		# 物理功能源节点
				s = match[s_vnf]						# 映射的具体节点
				if s == d:		# 最后一个功能部署在宿节点	
					all_best_paths.append(copy.deepcopy([]))
					continue
			else:
				s_vnf = eval(row['vnf_order'])[i-1]			# 物理功能源节点
				d_vnf = eval(row['vnf_order'])[i]			# 物理功能宿节点
				s = match[s_vnf]		# 映射的具体节点
				d = match[d_vnf]		# 映射的具体节点

			k_paths = self.k_shortest_paths(s, d)		# k条最短路
			best_path = self.bip_find_best_path(row, k_paths)		# k条最短路中的最好路
			if len(best_path) == 0:			# 找不到合适的路
				all_best_paths = []
				return all_best_paths		# 直接返回空
			all_best_paths.append(copy.deepcopy(best_path))
		return all_best_paths

	# 单业务处理函数，判断是否能接入，如果能接入，返回节点映射及链路集合
	def bip_is_req_access(self, row):
		is_access = True		# 是否成功接入
		match = self.bip_find_node(row)		# 找到节点映射关系
		is_node = self.bip_judge_node(match, row)		# 判断该关系是否可行
		if not is_node:
			is_access = False
			match = {}
			all_best_paths = []
			return is_access, match, all_best_paths

		# 找到所有最好的路径，每两个网络功能之间均有一条
		all_best_paths = self.bip_find_paths(row, match)
		if len(all_best_paths) == 0:		# 找不到所有满足条件的路径集合
			is_access = False
			match = {}
			all_best_paths = []
			return is_access, match, all_best_paths			
		return is_access, match, all_best_paths
	
	# 单业务处理函数，业务到达
	def bip_sig_req_arriv(self, row):
		is_access, match, all_best_paths = self.bip_is_req_access(row)
		print('match from upper')
		print(match)
		print('match from upper')
		req_no = int(row['req_no'])
		self.vm_idx[req_no] = []
		self.vm_idx[req_no].append(is_access)
		self.vm_idx[req_no].append(copy.deepcopy(match))
		self.vm_idx[req_no].append(copy.deepcopy(all_best_paths))
		if is_access:
			self.fill_node_load(row)
			self.fill_edge_load(row)
		else:
			pass

	# 单业务处理函数，业务离开
	def bip_sig_req_leave(self, row):
		req_no = int(row['req_no'])
		is_access = self.vm_idx[req_no]
		if is_access:
			self.rele_node_load(row)
			self.rele_edge_load(row)
		else:
			pass

	# 业务处理函数，二部图方法
	def bip_req_process(self):
		self.read_topo_file()
		self.topo_init()
		for idx, row in self.traff_df.iterrows():
			if row['status'] == 'arriv':		# 到达
				self.bip_sig_req_arriv(row)
				break
			else:								# 离开
				self.bip_sig_req_leave(row)

		print(self.node_load)
		print(self.edge_load)


# 主函数
if __name__ == '__main__':
	emb = Embedding()
	# emb.traff_sort()
	emb.read_topo_file()
	emb.topo_init()
	# emb.traff_df.to_excel('traffic.xlsx', index = False)
	emb.bip_req_process()
