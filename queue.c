#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "harness.h"
#include "queue.h"

/* Notice: sometimes, Cppcheck would find the potential NULL pointer bugs,
 * but some of them cannot occur. You can suppress them by adding the
 * following line.
 *   cppcheck-suppress nullPointer
 */

/*
 * Create empty queue.
 * Return NULL if could not allocate space.
 */
struct list_head *q_new()
{
    struct list_head *q = malloc(sizeof(struct list_head));
    if (!q)
        return NULL;

    INIT_LIST_HEAD(q);
    return q;
}

/* Free all storage used by queue */
void q_free(struct list_head *l)
{
    if (!l)
        return;

    element_t *entry, *safe;

    list_for_each_entry_safe (entry, safe, l, list)
        q_release_element(entry);
    free(l);
}

/*
 * Allocate space for new element and copy the string to it.
 * Return NULL if could not allocate space.
 */
element_t *q_new_element(char *s)
{
    element_t *q = malloc(sizeof(element_t));
    if (!q)
        return NULL;

    q->value = malloc(strlen(s) + 1);
    if (!q->value) {
        free(q);
        return NULL;
    }

    strncpy(q->value, s, strlen(s) + 1);
    return q;
}

/*
 * Attempt to insert element at head of queue.
 * Return true if successful.
 * Return false if q is NULL or could not allocate space.
 * Argument s points to the string to be stored.
 * The function must explicitly allocate space and copy the string into it.
 */
bool q_insert_head(struct list_head *head, char *s)
{
    if (!head)
        return false;

    element_t *ele = q_new_element(s);
    if (!ele)
        return false;

    list_add(&ele->list, head);
    return true;
}

/*
 * Attempt to insert element at tail of queue.
 * Return true if successful.
 * Return false if q is NULL or could not allocate space.
 * Argument s points to the string to be stored.
 * The function must explicitly allocate space and copy the string into it.
 */
bool q_insert_tail(struct list_head *head, char *s)
{
    if (!head)
        return false;

    element_t *ele = q_new_element(s);
    if (!ele)
        return false;

    list_add_tail(&ele->list, head);
    return true;
}

/*
 * Attempt to remove element from head of queue.
 * Return target element.
 * Return NULL if queue is NULL or empty.
 * If sp is non-NULL and an element is removed, copy the removed string to *sp
 * (up to a maximum of bufsize-1 characters, plus a null terminator.)
 *
 * NOTE: "remove" is different from "delete"
 * The space used by the list element and the string should not be freed.
 * The only thing "remove" need to do is unlink it.
 *
 * REF:
 * https://english.stackexchange.com/questions/52508/difference-between-delete-and-remove
 */
element_t *q_remove_head(struct list_head *head, char *sp, size_t bufsize)
{
    if (!head || head->next == head)
        return NULL;  // Queue is NULL or empty

    element_t *ele = list_entry(head->next, element_t, list);
    head->next->next->prev = head;
    head->next = head->next->next;
    if (sp) {
        strncpy(sp, ele->value, bufsize - 1);
        sp[bufsize - 1] = '\0';
    }
    return ele;
}

/*
 * Attempt to remove element from tail of queue.
 * Other attribute is as same as q_remove_head.
 */
element_t *q_remove_tail(struct list_head *head, char *sp, size_t bufsize)
{
    if (!head || head->next == head)
        return NULL;  // Queue is NULL or empty

    element_t *ele = list_entry(head->prev, element_t, list);
    head->prev->prev->next = head;
    head->prev = head->prev->prev;
    if (sp) {
        strncpy(sp, ele->value, bufsize - 1);
        sp[bufsize - 1] = '\0';
    }
    return ele;
}

/*
 * WARN: This is for external usage, don't modify it
 * Attempt to release element.
 */
void q_release_element(element_t *e)
{
    free(e->value);
    free(e);
}

/*
 * Return number of elements in queue.
 * Return 0 if q is NULL or empty
 */
int q_size(struct list_head *head)
{
    if (!head)
        return 0;

    int len = 0;
    struct list_head *li;

    list_for_each (li, head)
        len++;
    return len;
}

/*
 * Delete the middle node in list.
 * The middle node of a linked list of size n is the
 * ⌊n / 2⌋th node from the start using 0-based indexing.
 * If there're six element, the third member should be return.
 * Return true if successful.
 * Return false if list is NULL or empty.
 */
bool q_delete_mid(struct list_head *head)
{
    // https://leetcode.com/problems/delete-the-middle-node-of-a-linked-list/
    if (!head || head->next == head)
        return NULL;  // Queue is NULL or empty

    int mid = q_size(head) / 2;
    struct list_head *pos = head->next;
    for (int i = 0; i < mid; i++)  // pos will stop at middle node
        pos = pos->next;
    pos->next->prev = pos->prev;
    pos->prev->next = pos->next;
    q_release_element(list_entry(pos, element_t, list));
    return true;
}

/*
 * Delete all nodes that have duplicate string,
 * leaving only distinct strings from the original list.
 * Return true if successful.
 * Return false if list is NULL.
 *
 * Note: this function always be called after sorting, in other words,
 * list is guaranteed to be sorted in ascending order.
 */
bool q_delete_dup(struct list_head *head)
{
    // https://leetcode.com/problems/remove-duplicates-from-sorted-list-ii/
    if (!head)
        return false;

    struct list_head *slow = head->next, *fast = head->next->next, *del = NULL,
                     *tmp = NULL;
    for (; fast != head && fast != head->next;
         slow = slow->next, fast = slow->next) {
        if (strcmp(list_entry(slow, element_t, list)->value,
                   list_entry(fast, element_t, list)->value) == 0) {
            while (fast->next != head &&
                   strcmp(list_entry(fast, element_t, list)->value,
                          list_entry(fast->next, element_t, list)->value) == 0)
                fast = fast->next;
            // slow:node before duplicate sub queue
            // fast:node after duplicate sub queue
            slow = slow->prev;
            fast = fast->next;
            // release duplicate nodes
            for (del = slow->next; del != fast; del = tmp) {
                tmp = del->next;
                q_release_element(list_entry(del, element_t, list));
            }
            // link `slow` and `fast`
            slow->next = fast;
            fast->prev = slow;
        }
    }
    return true;
}

/*
 * Attempt to swap every two adjacent nodes.
 */
void q_swap(struct list_head *head)
{
    // https://leetcode.com/problems/swap-nodes-in-pairs/
    if (!head || q_size(head) < 2)
        return;  // Queue is NULL or less than 2 node

    for (struct list_head *slow = head->next, *fast = head->next->next;
         fast != head && fast != head->next;
         slow = slow->next, fast = slow->next) {
        slow->prev->next = fast;
        fast->next->prev = slow;
        slow->next = fast->next;
        fast->prev = slow->prev;
        slow->prev = fast;
        fast->next = slow;
    }
}

/*
 * Reverse elements in queue
 * No effect if q is NULL or empty
 * This function should not allocate or free any list elements
 * (e.g., by calling q_insert_head, q_insert_tail, or q_remove_head).
 * It should rearrange the existing ones.
 */
void q_reverse(struct list_head *head)
{
    if (!head)
        return;

    struct list_head *node, *safe;

    list_for_each_safe (node, safe, head) {
        node->next = node->prev;
        node->prev = safe;
    }
    safe = head->prev;
    head->prev = head->next;
    head->next = safe;
}

/*
 * Merge 2 sorted queue
 * Design singly linked list
 * Repair prev link and circular after merge (for doubly circular linked list)
 * Return the head if success otherwise return NULL
 */
struct list_head *merge_2_Queue(struct list_head *L1, struct list_head *L2)
{
    struct list_head *head = NULL, **ptr = &head, **node = NULL;
    for (; L1 && L2; ptr = &(*ptr)->next, *node = (*node)->next) {
        node = strcmp(list_entry(L1, element_t, list)->value,
                      list_entry(L2, element_t, list)->value) < 0
                   ? &L1
                   : &L2;
        *ptr = *node;
    }
    *ptr = (struct list_head *) ((uintptr_t) L1 | (uintptr_t) L2);
    return head;
}

/*
 * Sort elements of queue in ascending order
 * No effect if q is NULL or empty. In addition, if q has only one
 * element, do nothing.
 */
void q_sort(struct list_head *head)
{
    if (!head || q_size(head) < 2)
        return;  // Queue is NULL or less than 2 node

    // devide
    int queueSize = 0;
    struct list_head *queue[10000] = {NULL};
    for (struct list_head *tmp = head->next->next; tmp != head->next;
         tmp = tmp->next) {
        tmp->prev->next = NULL;
        tmp->prev->prev = NULL;
        queue[queueSize++] = tmp->prev;
    }

    // merge and sort
    while (queueSize > 1) {
        for (int i = 0, j = queueSize - 1; i < j; i++, j--)
            queue[i] = merge_2_Queue(queue[i], queue[j]);
        queueSize = (queueSize + 1) / 2;
    }

    // repair prev links and circular
    head->next = queue[0];
    struct list_head *tmp = head;
    for (; tmp->next != NULL; tmp = tmp->next)
        tmp->next->prev = tmp;
    tmp->next = head;
    head->prev = tmp;
}
