#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>

typedef struct centroid {
  float x;
  float y;
  float mass;
} centroid;

typedef struct quad {
  float width;
  float left;
  float top;
  centroid *center;
} quad;

typedef struct qtree {
  struct quad *square;
  struct qtree *tl;
  struct qtree *tr;
  struct qtree *bl;
  struct qtree *br;
} qtree;

int in_bounding_box(float x, float y, struct quad *startingQuad) {
  if (x < startingQuad->left || x > (startingQuad->left + startingQuad->width) || y < startingQuad->top || y > (startingQuad->top + startingQuad->width)) {
    return 0;
  }
  return 1;
}

// 1 is top left, 2 is top right, 3 is bottom left, 4 is bottom right
int which_quad(float x, float y, struct quad *startingQuad) {
  if (x <= (startingQuad->left + startingQuad->width / 2.0F) && y < (startingQuad->top + startingQuad->width / 2.0F)) {
    return 1;
  } else if (x > (startingQuad->left + startingQuad->width / 2.0F) && y < (startingQuad->top + startingQuad->width / 2.0F)) {
    return 2;
  } else if (x <= (startingQuad->left + startingQuad->width / 2.0F) && y >= (startingQuad->top + startingQuad->width / 2.0F)) {
    return 3;
  } else {
    return 4;
  }
}

centroid* centroid_sum(centroid *centroid1, centroid *centroid2) {
  if (centroid1 == NULL) {
    return centroid2;
  } else if (centroid2 == NULL) {
    return centroid1;
  }
  centroid *newCentroid = (centroid*) malloc(sizeof(centroid));
  float mass = centroid1->mass + centroid2->mass;
  newCentroid->mass = mass;
  float newX = (1.0F / mass) * (centroid1->mass * centroid1->x + centroid2->mass * centroid2->x);
  newCentroid->x = newX;
  float newY = (1.0F / mass) * (centroid1->mass * centroid1->y + centroid2->mass * centroid2->y);
  newCentroid->y = newY;
  return newCentroid;
}

int compare_float(float f1, float f2) {
  float precision = 0.00001F;
  if (((f1 - precision) < f2) && 
      ((f1 + precision) > f2)) {
    return 1;
  }
  else {
    return 0;
  }
}

int is_in_box(qtree *tree, float x, float y) {
  if (tree->square == NULL) {
    return 0;
  } else if (tree->tl == NULL && tree->tr == NULL && tree->bl == NULL && tree->br == NULL) {
    if (compare_float(tree->square->center->x, x) && compare_float(tree->square->center->y, y)) {
      return 1;
    }
    return 0;
  } else {
    if (compare_float(tree->square->center->x, x) && compare_float(tree->square->center->y, y)) {
	return 1;
    }
    int newBox = which_quad(x, y, tree->square);
    if (newBox == 1) {
      return is_in_box(tree->tl, x, y);
    } else if (newBox == 2) {
      return is_in_box(tree->tr, x, y);
    } else if (newBox == 3) {
      return is_in_box(tree->bl, x, y);
    } else if (newBox == 4) {
      return is_in_box(tree->br, x, y);
    }
    return 0;
  }
}

qtree* empty_qtree(float x, float y, float mass, float width, float top, float left) {
  qtree *tree = (qtree*) malloc(sizeof(qtree));
  tree->tl = NULL;
  tree->tr = NULL;
  tree->bl = NULL;
  tree->br = NULL;
  quad *squ = (quad*) malloc(sizeof(quad));
  centroid *cent = (centroid*) malloc(sizeof(centroid));
  tree->square = squ;
  tree->square->center = cent;
  tree->square->width = width;
  tree->square->left = left;
  tree->square->top = top;
  tree->square->center->x = x;
  tree->square->center->y = y;
  tree->square->center->mass = mass;
  return tree;
}

qtree* insertPoint(float x, float y, qtree *tree, float mass) {
  if (tree == NULL) {
    tree = empty_qtree(x, y, mass, 4.0F, 0.0F, 0.0F);
    int which = which_quad(x, y, tree->square);
    qtree* node;
  } else if (tree->square->center->x == x && tree->square->center->y == y) {
    tree->square->center->mass = tree->square->center->mass + mass;
  } else if (which_quad(x, y, tree->square) == 1 && tree->tl == NULL) {
    if (tree->tl == NULL && tree->tr == NULL &&  tree->bl == NULL &&  tree->br == NULL) {
      float oldx = tree->square->center->x;
      float oldy = tree->square->center->y;
      float oldmass = tree->square->center->mass;
      float oldquad = which_quad(oldx, oldy, tree->square);
      qtree* subnode; 
      if (oldquad == 1) {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top, tree->square->left);
	tree->tl = subnode;
      } else if (oldquad == 3) {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top + tree->square->width / 2.0F, tree->square->left);
	tree->bl = subnode;
      } else if (oldquad == 2) {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top, tree->square->left + tree->square->width / 2.0F);
	tree->tr = subnode;
      } else {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top + tree->square->width / 2.0F, tree->square->left + tree->square->width / 2.0F);
	tree->br = subnode;
      }
    }
    float width = tree->square->width;
    if (tree->tl == NULL) {
      tree->tl = empty_qtree(x, y, mass, width / 2.0F, tree->square->top, tree->square->left);
    } else {
      insertPoint(x, y, tree->tl, mass);
    }
    centroid* output;
    if (tree->tr != NULL) {
      output = centroid_sum(tree->tl->square->center, tree->tr->square->center);
      if (tree->br != NULL) {
	output = centroid_sum(output, tree->br->square->center);
      }
      if (tree->bl != NULL) {
	output = centroid_sum(output, tree->bl->square->center);
      }
    } else if (tree->bl != NULL) {
      output = centroid_sum(tree->tl->square->center, tree->bl->square->center);
      if (tree->br != NULL) {
	output = centroid_sum(output, tree->br->square->center);
      }
    } else if (tree->br != NULL) {
      output = centroid_sum(tree->tl->square->center, tree->br->square->center);
    } else {
      output = tree->tl->square->center;
    }
    tree->square->center = output;
  } else if (which_quad(x, y, tree->square) == 2 && tree->tr == NULL) {
    if (tree->tl == NULL && tree->tr == NULL &&  tree->bl == NULL &&  tree->br == NULL) {
      float oldx = tree->square->center->x;
      float oldy = tree->square->center->y;
      float oldmass = tree->square->center->mass;
      float oldquad = which_quad(oldx, oldy, tree->square);
      qtree* subnode; 
      if (oldquad == 1) {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top, tree->square->left);
	tree->tl = subnode;
      } else if (oldquad == 3) {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top + tree->square->width / 2.0F, tree->square->left);
	tree->bl = subnode;
      } else if (oldquad == 2) {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top, tree->square->left + tree->square->width / 2.0F);
	tree->tr = subnode;
      } else {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top + tree->square->width / 2.0F, tree->square->left + tree->square->width / 2.0F);
	tree->br = subnode;
      }
    }
    float width = tree->square->width;
    if (tree->tr == NULL) {
      tree->tr = empty_qtree(x, y, mass, width / 2.0F, tree->square->top, tree->square->left + width / 2.0F);
    } else {
      insertPoint(x, y, tree->tr, mass);
    }
    centroid* output;
    if (tree->tl != NULL) {
      output = centroid_sum(tree->tl->square->center, tree->tr->square->center);
      if (tree->br != NULL) {
	output = centroid_sum(output, tree->br->square->center);
      }
      if (tree->bl != NULL) {
	output = centroid_sum(output, tree->bl->square->center);
      }
    } else if (tree->br != NULL) {
      output = centroid_sum(tree->tr->square->center, tree->br->square->center);
      if (tree->bl != NULL) {
	output = centroid_sum(output, tree->bl->square->center);
      }
    } else if (tree->bl != NULL) {
      output = centroid_sum(tree->tr->square->center, tree->bl->square->center);
    } else {
      output = tree->tr->square->center;
    }
    tree->square->center = output;
  } else if (which_quad(x, y, tree->square) == 3 && tree->bl == NULL) {
    if (tree->tl == NULL && tree->tr == NULL &&  tree->bl == NULL &&  tree->br == NULL) {
      float oldx = tree->square->center->x;
      float oldy = tree->square->center->y;
      float oldmass = tree->square->center->mass;
      float oldquad = which_quad(oldx, oldy, tree->square);
      qtree* subnode; 
      if (oldquad == 1) {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top, tree->square->left);
	tree->tl = subnode;
      } else if (oldquad == 3) {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top + tree->square->width / 2.0F, tree->square->left);
	tree->bl = subnode;
      } else if (oldquad == 2) {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top, tree->square->left + tree->square->width / 2.0F);
	tree->tr = subnode;
      } else {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top + tree->square->width / 2.0F, tree->square->left + tree->square->width / 2.0F);
	tree->br = subnode;
      }
    }
    float width = tree->square->width;
    if (tree->bl == NULL) {
      tree->bl = empty_qtree(x, y, mass, width / 2.0F, tree->square->top + width / 2.0F, tree->square->left);
    } else {
      insertPoint(x, y, tree->bl, mass);
    }
    centroid* output;
    if (tree->tl != NULL) {
      output = centroid_sum(tree->tl->square->center, tree->bl->square->center);
      if (tree->tr != NULL) {
	output = centroid_sum(output, tree->tr->square->center);
      }
      if (tree->br != NULL) {
	output = centroid_sum(output, tree->br->square->center);
      }
    } else if (tree->tr != NULL) {
      output = centroid_sum(tree->tr->square->center, tree->bl->square->center);
      if (tree->br != NULL) {
	output = centroid_sum(output, tree->br->square->center);
      }
    } else if (tree->br != NULL) {
      output = centroid_sum(tree->bl->square->center, tree->br->square->center);
    } else {
      output = tree->bl->square->center;
    }
    tree->square->center = output;
  } else if (which_quad(x, y, tree->square) == 4 && tree->br == NULL) {
    if (tree->tl == NULL && tree->tr == NULL &&  tree->bl == NULL &&  tree->br == NULL) {
      float oldx = tree->square->center->x;
      float oldy = tree->square->center->y;
      float oldmass = tree->square->center->mass;
      float oldquad = which_quad(oldx, oldy, tree->square);
      qtree* subnode; 
      if (oldquad == 1) {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top, tree->square->left);
	tree->tl = subnode;
      } else if (oldquad == 3) {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top + tree->square->width / 2.0F, tree->square->left);
	tree->bl = subnode;
      } else if (oldquad == 2) {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top, tree->square->left + tree->square->width / 2.0F);
	tree->tr = subnode;
      } else {
	subnode = empty_qtree(oldx, oldy, oldmass, tree->square->width / 2.0F, tree->square->top + tree->square->width / 2.0F, tree->square->left + tree->square->width / 2.0F);
	tree->br = subnode;
      }
    }
    float width = tree->square->width;
    if (tree->br == NULL) {
      tree->br = empty_qtree(x, y, mass, width / 2.0F, tree->square->top + width / 2.0F, tree->square->left + width / 2.0F);
    } else {
      insertPoint(x, y, tree->br, mass);
    }
    centroid* output;
    if (tree->tl != NULL) {
      output = centroid_sum(tree->tl->square->center, tree->br->square->center);
      if (tree->tr != NULL) {
	output = centroid_sum(output, tree->tr->square->center);
      }
      if (tree->bl != NULL) {
	output = centroid_sum(output, tree->bl->square->center);
      }
    } else if (tree->tr != NULL) {
      output = centroid_sum(tree->tr->square->center, tree->br->square->center);
      if (tree->bl != NULL) {
	output = centroid_sum(output, tree->bl->square->center);
      }
    } else if (tree->bl != NULL) {
      output = centroid_sum(tree->bl->square->center, tree->br->square->center);
    } else {
      output = tree->br->square->center;
    }
    tree->square->center = output;
  } else if (which_quad(x, y, tree->square) == 1) {
    tree->tl = insertPoint(x, y, tree->tl, mass);
    centroid* output;
    if (tree->tr != NULL) {
      output = centroid_sum(tree->tl->square->center, tree->tr->square->center);
      if (tree->br != NULL) {
	output = centroid_sum(output, tree->br->square->center);
      }
      if (tree->bl != NULL) {
	output = centroid_sum(output, tree->bl->square->center);
      }
    } else if (tree->bl != NULL) {
      output = centroid_sum(tree->tl->square->center, tree->bl->square->center);
      if (tree->br != NULL) {
	output = centroid_sum(output, tree->br->square->center);
      }
    } else if (tree->br != NULL) {
      output = centroid_sum(tree->tl->square->center, tree->br->square->center);
    } else {
      output = tree->tl->square->center;
    }
    tree->square->center = output;
  } else if (which_quad(x, y, tree->square) == 2) {
    tree->tr = insertPoint(x, y, tree->tr, mass);
    centroid* output;
    if (tree->tl != NULL) {
      output = centroid_sum(tree->tl->square->center, tree->tr->square->center);
      if (tree->br != NULL) {
	output = centroid_sum(output, tree->br->square->center);
      }
      if (tree->bl != NULL) {
	output = centroid_sum(output, tree->bl->square->center);
      }
    } else if (tree->br != NULL) {
      output = centroid_sum(tree->tr->square->center, tree->br->square->center);
      if (tree->bl != NULL) {
	output = centroid_sum(output, tree->bl->square->center);
      }
    } else if (tree->bl != NULL) {
      output = centroid_sum(tree->tr->square->center, tree->bl->square->center);
    } else {
      output = tree->tr->square->center;
    }
    tree->square->center = output;
  } else if (which_quad(x, y, tree->square) == 3) {
    tree->bl = insertPoint(x, y, tree->bl, mass);
    centroid* output;
    if (tree->tl != NULL) {
      output = centroid_sum(tree->tl->square->center, tree->bl->square->center);
      if (tree->tr != NULL) {
	output = centroid_sum(output, tree->tr->square->center);
      }
      if (tree->br != NULL) {
	output = centroid_sum(output, tree->br->square->center);
      }
    } else if (tree->tr != NULL) {
      output = centroid_sum(tree->tr->square->center, tree->bl->square->center);
      if (tree->br != NULL) {
	output = centroid_sum(output, tree->br->square->center);
      }
    } else if (tree->br != NULL) {
      output = centroid_sum(tree->bl->square->center, tree->br->square->center);
    } else {
      output = tree->bl->square->center;
    }
    tree->square->center = output;
  } else if (which_quad(x, y, tree->square) == 4) {
    tree->br = insertPoint(x, y, tree->br, mass);
    centroid* output;
    if (tree->tl != NULL) {
      output = centroid_sum(tree->tl->square->center, tree->br->square->center);
      if (tree->tr != NULL) {
	output = centroid_sum(output, tree->tr->square->center);
      }
      if (tree->bl != NULL) {
	output = centroid_sum(output, tree->bl->square->center);
      }
    } else if (tree->tr != NULL) {
      output = centroid_sum(tree->tr->square->center, tree->br->square->center);
      if (tree->bl != NULL) {
	output = centroid_sum(output, tree->bl->square->center);
      }
    } else if (tree->tr != NULL) {
      output = centroid_sum(tree->tr->square->center, tree->br->square->center);
    } else {
      output = tree->br->square->center;
    }
    tree->square->center = output;
  }
  return tree;
}

int body() {
  // implement the acceleration

  // test q4 tree from 120 examples
  int t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15;
  t1 = 0;
  t2 = 0;
  t3 = 0;
  t4 = 0;
  t5 = 0;
  t6 = 0;
  t7 = 0;
  t8 = 0;
  t9 = 0;
  t10 = 0;
  t11 = 0;
  t12 = 0;
  t13 = 0;
  t14 = 0;
  t15 = 0;
  qtree* tree = NULL;
  tree = insertPoint(1.5F, 2.5F, tree, 1.0F);
  tree = insertPoint(2.1F, 2.1F, tree, 1.0F);
  tree = insertPoint(1.0F, 1.0F, tree, 2.0F);
  if (compare_float(tree->square->center->x, 1.4F) && compare_float(tree->square->center->y, 1.65F) && compare_float(tree->square->center->mass, 4.0F)) {
    t1 = 1;
  }
  
  tree = insertPoint(2.6F, 2.8F, tree, 1.0F);
  if (compare_float(tree->br->tl->br->square->center->x, 2.6F) && compare_float(tree->br->tl->br->square->center->y, 2.8F) && compare_float(tree->br->tl->br->square->center->mass, 1.0F)) {
    t2 = 1;
  }
  if (compare_float(tree->tl->square->center->x, 1.0F) && compare_float( tree->tl->square->center->y, 1.0F) && compare_float( tree->tl->square->center->mass, 2.0F)) {
    t3 = 1;
  }
  if (compare_float(tree->bl->square->center->x, 1.5F) && compare_float( tree->bl->square->center->y, 2.5F) && compare_float(tree->bl->square->center->mass, 1.0F)) {
    t4 = 1;
  }
  if (compare_float(tree->br->tl->tl->square->center->x, 2.1F) && compare_float(tree->br->tl->tl->square->center->y, 2.1F) && compare_float(tree->br->tl->tl->square->center->mass, 1.0F)) {
    t5 = 1;
  }
  if (compare_float(tree->br->tl->square->center->x, 2.35F) && compare_float(tree->br->tl->square->center->y, 2.45F) && compare_float(tree->br->tl->square->center->mass, 2.0F)) {
    t6 = 1;
  }
  if (compare_float(tree->square->center->x, 1.64F) && compare_float(tree->square->center->y, 1.88F) && compare_float(tree->square->center->mass, 5.0F)) {
    t7 = 1;
  }

  // test tree add same node twice
  qtree* tree2 = NULL;
  tree2 = insertPoint(1.0F, 1.0F, tree2, 1.0F);
  tree2 = insertPoint(1.0F, 1.0F, tree2, 1.0F);
  if (compare_float(tree2->square->center->mass, 2.0F)) {
    t8 = 1;
  }

  // recurse alot case
  qtree* tree3 = NULL;
  tree3 = insertPoint(0.0F, 0.0F, tree3, 1.0F);
  tree3 = insertPoint(0.2F, 0.2F, tree3, 1.0F);
  if (compare_float(tree3->square->center->x, 0.1F) && compare_float(tree3->square->center->y, 0.1F) && compare_float(tree3->square->center->mass, 2.0F)) {
    t9 = 1;
  }
  if (compare_float(tree3->tl->square->center->x, 0.1F) && compare_float(tree3->tl->square->center->y, 0.1F) && compare_float(tree3->tl->square->center->mass, 2.0F)) {
    t10 = 1;
  }
  if (compare_float(tree3->tl->tl->square->center->x, 0.1F) && compare_float(tree3->tl->tl->square->center->y, 0.1F) && compare_float(tree3->tl->tl->square->center->mass, 2.0F)) {
    t11 = 1;
  }
  if (compare_float(tree3->tl->tl->tl->square->center->x, 0.1F) && compare_float(tree3->tl->tl->tl->square->center->y, 0.1F) && compare_float(tree3->tl->tl->tl->square->center->mass, 2.0F)) {
    t12 = 1;
  }
  if (compare_float(tree3->tl->tl->tl->tl->square->center->x, 0.1F) && compare_float(tree3->tl->tl->tl->tl->square->center->y, 0.1F) && compare_float(tree3->tl->tl->tl->tl->square->center->mass, 2.0F)) {
    t13 = 1;
  }
  if (compare_float(tree3->tl->tl->tl->tl->tl->square->center->x, 0.0F) && compare_float(tree3->tl->tl->tl->tl->tl->square->center->y, 0.0F) && compare_float(tree3->tl->tl->tl->tl->tl->square->center->mass, 1.0F)) {
    t14 = 1;
  }
  if (compare_float(tree3->tl->tl->tl->tl->br->square->center->x, 0.2F) && compare_float(tree3->tl->tl->tl->tl->br->square->center->y, 0.2F) && compare_float(tree3->tl->tl->tl->tl->br->square->center->mass, 1.0F)) {
    t15 = 1;
  }

  int returnVal = 0;
  if (t1 && t2 && t3 && t4 && t5 && t6 && t7 && t8 && t9 && t10 && t11 && t12 && t13 && t14 && t15) {
    returnVal = 1;
  }
  return returnVal;
}

int main(int argc, char *argv[]) {
  int val = body();
  return body();
}


