#include <iostream>
#include <stdio.h>
#include <math.h>
#include <vector>
#include <algorithm>
#include <set>
#include <map>
#include <queue>
#include <string>
#include <cstring>
#include <queue>
#define VISITED 1
#define UNVISITED -1
#define INF -1
#define BFS 0
#define DFS 1
#define TOPO 2
#define type_EdgeList 0
#define type_AdjList 1
#define FOR(i,a,b) for(int i=a;i<b;i++)
#define print_vec(vec) for(int i : vec) printf("%d ", i);
#define printEdgeList(edgeList) for(pair<int, ii> i : edgeList) printf("%d %d %d \n", i.second.first, i.second.second, i.first);
using namespace std;
typedef pair<int, int> ii; // pair of integers
typedef vector<int> vi; // vector of integers
typedef vector<vi> vvi; // vector of vector of integers
typedef vector<ii> vii; // vector of pair of integers
//C++ implementation of UnionFind.
class UnionFind {
	private : 
		vi p, rank;
	public:
		UnionFind(int N){
			rank.assign(N,0);
			p.assign(N,0);
			FOR(i,0,N) p[i] = i;
		};
		int findSet(int i){
			return (p[i]==i) ? i : (p[i]=findSet(p[i]));
		}
		bool isSameSet(int i, int j) {return findSet(i) == findSet(j);}
		void unionSet(int i, int j){
			if(!isSameSet(i,j)){
				int x = findSet(i),y=findSet(j);
				if(rank[x] > rank[y]) p[y] = x;
				else{
					p[x]= y;
					if(rank[x] == rank[y])rank[y]++;
				}
			}
		}
};
//C++ implementation of graph.
class Graph {
	private : 
		vector<vii> AdjList;
		vi dfs_num;
		vi distance;
		vi bfs_vector;
		vi dfs_vector;
		vi topo_sort;
		vi in_degree;
		vi color;
		vector< pair<int,ii> > EdgeList;
		int num_vertices;
		int num_comp;
		int num_edges;		
	public :
	//Constructor : 
	Graph(int v, int e){
		//Do not use reserve. it doesnot allocate the memory as such and cause lot of problems.
		//Always use resize().
		dfs_num.resize(v);
		AdjList.resize(v);
		distance.resize(v);
		in_degree.resize(v);
		color.resize(v);
		fill(dfs_num.begin(),dfs_num.end(),UNVISITED);
		fill(distance.begin(),distance.end(),INF);
		fill(in_degree.begin(),in_degree.end(),0);
		fill(color.begin(),color.end(),INF);
		num_vertices = v;
		num_edges = e;
		num_comp = 0;
	};
	
	void insert_edge(int a, int b, int weight=0, int type=type_AdjList, bool directed=false){
		AdjList[a].push_back( ii(b, weight) );		
		//if graph is undirected
		if(!directed){
			AdjList[b].push_back( ii(a, weight) );
		}
		//this is mainly used only when MST is to be formed and in that case...
		//...we need the edges in sorted order.
		if(type == type_EdgeList){
			EdgeList.push_back(make_pair(weight, ii(a,b)));
		}
	}
	int min_span_tree() {
		int mst_cost = 0;
		if(EdgeList.size() != 0 ){
			sort(EdgeList.begin(),EdgeList.end());
			UnionFind UF(num_vertices);
			FOR(i,0,num_edges){
				pair<int,ii> front = EdgeList[i];
				if(!UF.isSameSet(front.second.first,front.second.second)){
					mst_cost += front.first;
					UF.unionSet(front.second.first,front.second.second);
				}
			}
		}
		return mst_cost;
	}
	
	//dfs recursive: can be implemented iteratively using stack
	void dfs(int u) {
		dfs_num[u] = VISITED;
		dfs_vector.push_back(u);
		FOR(i , 0, (int)AdjList[u].size()) {
			ii v = AdjList[u][i];
			if(dfs_num[v.first] == UNVISITED){
				dfs(v.first);
			}
		}
	};
	
	//bfs using queue
	void bfs(int u){
		distance[u] = 0;
		queue<int> q;
		q.push(u);
		while( !q.empty() ){
			int s = q.front(); q.pop();
			bfs_vector.push_back(s);
			FOR(i ,0 ,(int)AdjList[s].size()){
				ii v = AdjList[s][i];
				if(distance[v.first]==INF){
					distance[v.first] = distance[s] + 1;
					q.push(v.first);
				}
			}
		}
	};
	//Finding connected components
	void connected_components(){
		fill(dfs_num.begin(),dfs_num.end(),UNVISITED);
		FOR(i,0,num_vertices){
			if(dfs_num[i] == UNVISITED){
				dfs(i);
			}
		}
	};
	vi topo_sort_bfs(){
		//setting the proper in degrees
		FOR(i,0,num_vertices){
			for(ii v: AdjList[i]){
				in_degree[v.first]++;
			}
		}
		//Creating queue and pushing all vertices with indegree 0 to it
		queue<int> q;
		FOR(i,0,num_vertices){
			if(in_degree[i]==0){
				q.push(i);
			}
		}
		vi topo_order;
		int count = 0;
		
		while(!q.empty()){
			int front = q.front();
			q.pop();
			topo_order.push_back(front);
			for(ii p : AdjList[front]){
				if(--in_degree[p.first] == 0 ) q.push(p.first);
			}
			count++;
		}
		return topo_order;
	};
	bool bipartite_check(int s){
		color[s] = 0;
		queue<int> q;
		q.push(s);
		bool isBipartite = true;
		while( !q.empty() & isBipartite){
			int u = q.front(); q.pop();
			FOR(i ,0 ,(int)AdjList[u].size()){
				ii v = AdjList[u][i];
				if(color[v.first]==INF){
					color[v.first] = 1-color[u];
					q.push(v.first);
				} else if(color[v.first] == color[u]){
					isBipartite = false; 
					break;
				}
			}
		}
		return isBipartite;
	};
	bool bipartite_check_all(){
		bool ans = true;
		FOR(i,0,num_vertices){
			if(color[i]==INF){
				ans = bipartite_check(i);
				if(!ans){
					break;
				}
			}
		}
		return ans;
	};

	int bellman_ford(int s, int t){
		distance[s] = 0;
		for (int i = 0; i < num_vertices - 1; i++) 
			for (int u = 0; u < num_vertices; u++) 
				for (int j = 0; j < (int)AdjList[u].size(); j++) {
					ii v = AdjList[u][j];
					distance[v.first] = min(distance[v.first], distance[u] + v.second);
				}
		return distance[t];
	};

	int dijksra (int s, int t) {
		distance[s] = 0; 
		priority_queue< ii, vector<ii>, greater<ii> > pq; 
		pq.push(ii(0, s));
		while (!pq.empty()) { 
			ii front = pq.top();
			pq.pop();
			int d = front.first, u = front.second;
			if (d > distance[u]) continue;
			for (int j = 0; j < (int)AdjList[u].size(); j++) {
				ii v = AdjList[u][j];
				if (distance[u] + v.second < distance[v.first]) {
					distance[v.first] = distance[u] + v.second;
					pq.push(ii(distance[v.first], v.first));
				}
			}
		}
		return distance[t];
	}

	vi get_vec(int type){
		switch(type){
			case BFS:
				return  bfs_vector;
				break;
			case DFS : 
				return dfs_vector;
				break;
			case TOPO : 
				return topo_sort;
				break;
		}
	};
	
	//Just for debugging purpose
	void toString(){
		cout<<"Graph is " << endl;
		FOR(j,0,AdjList.size()){
			cout<<j<<" --> ";
			FOR(i,0,AdjList[j].size()){
				cout<<"("<<AdjList[j][i].first<<" ,"<<AdjList[j][i].first<<") ";
			}
			cout<<endl;
		}
	}
};
//driver program
int main(){
	return 0;
}