//#define _CRTDBG_MAP_ALLOC
#include <stdlib.h>
//#include <crtdbg.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <sys/timeb.h>

#include "graph.h"
#include "RmNonMax.h"

Graph gograph;

double gdmin_deg_ratio_o; // minimum out degree ratio threshold
double gdmin_deg_ratio_i; // minimum in degree ratio threshold
int gnmin_size; // minimum size threhsold
int gnmax_size; // (maximum size threhsold)
int gnmin_deg_o; // (min_size - 1) * gamma
int gnmin_deg_i;

void PrintSum(char* szgraph_file, int num_of_vertices);

int main(int argc, char *argv[])
{
	int narg_no, num_of_vertices;

	if(argc!=7)
	{
		printf("Usage:\n");
		printf("\t%s graph_file min_deg_ratio_out min_deg_ratio_in min_size nmax_size output_file\n", argv[0]);
		return 0;
	}

	narg_no = 2;
	gdmin_deg_ratio_o = atof(argv[narg_no]);
	narg_no++;
	gdmin_deg_ratio_i = atof(argv[narg_no]);
	narg_no++;
	printf("out ratio: %f, in ration: %f\n", gdmin_deg_ratio_o, gdmin_deg_ratio_i);
	if(gdmin_deg_ratio_o<=0 || gdmin_deg_ratio_o>1
			|| gdmin_deg_ratio_i<=0 || gdmin_deg_ratio_i>1)
	{
		printf("Please specify a positive number between 0 and 1 for the minimum degree ratio threshold\n");
		return 0;
	}

	gnmin_size = atoi(argv[narg_no]);
	narg_no++;
	if(gnmin_size<=0)
	{
		printf("Please specify a positive integer as the minimum size threhsold\n");
		return 0;
	}

	gnmax_size = atoi(argv[narg_no]);
	narg_no++;
	if(gnmax_size<=0)
	{
		printf("Please specify a positive integer as the maximum size threhsold\n");
		return 0;
	}

	gnmin_deg_o = (int)(gdmin_deg_ratio_o*(gnmin_size-1));
	if(gnmin_deg_o<gdmin_deg_ratio_o*(gnmin_size-1))
		gnmin_deg_o++;

	gnmin_deg_i = (int)(gdmin_deg_ratio_i*(gnmin_size-1));
	if(gnmin_deg_i<gdmin_deg_ratio_i*(gnmin_size-1))
		gnmin_deg_i++;

	if(gdmin_deg_ratio_o<1 || gdmin_deg_ratio_i<1)
	{
		num_of_vertices = gograph.Cliques(argv[1], "clq.temp.txt"); // main call !!!
		RemoveNonMax("clq.temp.txt", argv[narg_no]); // postprocessing to remove non-maximal qcqs
	}
	else 
	{
		num_of_vertices = gograph.Cliques(argv[1], argv[narg_no]);
		gntotal_max_cliques = gntotal_cliques;
	}

	PrintSum(argv[1], num_of_vertices);

//	_CrtDumpMemoryLeaks();

	return gntotal_max_cliques;
}


void PrintSum(char* szgraph_file, int num_of_vertices)
{
	FILE *fpsum;
	
	fpsum = fopen("qcliques-new.sum", "a+");
	if(fpsum==NULL)
	{
		printf("Error: cannot open file cliques.sum for write\n");
		return;
	}

	fprintf(fpsum, "%s %d %.3f %.3f %d\t", szgraph_file, num_of_vertices, gdmin_deg_ratio_o, gdmin_deg_ratio_i, gnmin_size);
	fprintf(fpsum, "%d %d %d\t", gnmax_clique_size, gntotal_cliques, gntotal_max_cliques);
	fprintf(fpsum, "%.3f %.3f\t", gdmining_time, gdrm_nonmax_time);
	fprintf(fpsum, "%d %d %d %d\t", gntotal_calls, gnmaxcheck_calls, gnum_of_condgraphs, gocondgraph_buf.ntotal_pages);
	fprintf(fpsum, "%d\t", gnlookahead_suceeds);
	fprintf(fpsum, "%d %d\t", gntotal_maxcheck_calls, gnmax_maxcheck_depth);
	fprintf(fpsum, "\n");

	fclose(fpsum);
}

