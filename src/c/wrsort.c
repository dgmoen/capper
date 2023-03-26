/*
 * Filename: wrsort.c
 *
 * Purpose: GTPlanet WRS results sorter
 *
 * Author: Dan Moen
 */
/***
   * Version history:
   * v1.00 1/1/11 : initial version? (started history late... better late than never)
   * v1.01 6/3/11 : added "Submitted" state for Disq: replay submitted but not checked
   * v1.10 11/23/11 : basic scoring support
   * v1.11 5/7/13 : "no harm handicap"; reduce weight history to 5 from 12
   * v1.12 8/7/13 : fix for 0 handicap for new racers
   * v2.00 1/13/14 : GT6 WRS, initial version
   * v2.01 1/27/14 : fix for first event
   * v2.02 2/17/14 : added "hybrid" curve
   * v2.03 5/12/14 : updated green/red/black flag URLs
   * v2.04 7/28/14 : changes to support ongoing handicapping
   * v2.05 8/17/14 : fixes for "no-damage" handicap
   * v2.06 9/1/14 : sort registry by handicap, not qualifier time
   * v2.07 6/1/17 : update flag URLs
   * v2.10 12/5/17 : GTSport changes
   * v2.11 12/5/17 : more GTSport changes
   * v2.12 1/2/18 : final "initial" GTSport changes
 ***/
// TODO:
// - compute recent history rating, straight and weighted
// - introduce CLI mode (when invoked with no parameters)
// -- add interactive watchlist
// -- add interactive promotion interface

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>

/************************************************/
/* defines */

#define MAX_LINE_LEN 512
#define MAX_STR_LEN 128
#define MAX_NAME_LEN 32
#define MAX_RACERS  2048
#define MAX_PLAYERS 2048
#define RACE_HISTORY 20 // count of "active" races
#define MAX_SPLITS  5
#define MAX_IMAGES  7
#define MAX_POINTS_PLACES  10 // maximum number of places earning points
#define MAX_RACER_POINTS   20 // maximum number of racers in the points table
#define MIN_POINTS 0 // minimum points awarded for a valid finish
#define MAX_SEASON_LENGTH 15

#define DIV_IN_USE  4 // maximum allowable division setting
#define DIV_COUNT   8 // number of division ranking calculated
#define DIV_ALL     0 // for iterator
#define ROOKIE_TIME 3 // events needed to lose rookie status

#define TRUE 1
#define FALSE 0

#define SUCCESS 1
#define FAILURE -1

#define BASE_DIV_PER_MIN 0.35f
#define DEFAULT_DIVISION_STEPPING 0.875f
#define DEFAULT_SQUEEZE 1.2f  // determines crowding, 1.2 = 5 divisions
#define DEFAULT_SCOOT  0.0f  // multiplied by zero par to adjust
#define AUTO_CYCLE_CNT 10 // number of cycles for auto squeeze/scoot calc
#define AUTO_SCOOT_FRACTION 5 // 1/x of submissions used for auto scoot
#define SUB_DIVISION_RANGE (1.0f/3.0f)
#define RATING_WEIGHT_CAP 5 // rating weight cap
#define MIN_PROMOTION_EVENT_COUNT 4 // minimum events completed prior to promo
#define NO_HARM_HANDICAP TRUE // prevent submission from harming handicap

#define NULL_PLAYER 0 // "safe" non-player ID
#define EVENT_QUALIFIER 0 // week 0 is qualifier

#define GTP_TAG "GTP"
#define DEFAULT_DB_NAME "gt7wrs.wdb"

/************************************************/
/* enum types */

typedef enum {
    RUN_MODE_EVENT, // normal mode
    RUN_MODE_QUALIFIER, // TBD
    RUN_MODE_REPORT, // check DB for promotions
    RUN_MODE_DB_FIX, // fix DB weight, etc
} run_mode_e;

typedef enum {
    SUB_DIV_GOLD,
    SUB_DIV_SILVER,
    SUB_DIV_BRONZE
} sub_div_e;

typedef enum {
    SHOW_NONE,
    SHOW_ALL_TIMES,
    SHOW_FLAGS,
    SHOW_RATINGS,
    SHOW_RATING_DELTA,
} display_opt_e;

typedef enum {
    // error
    LABEL_NONE,
    // general
    LABEL_COMMENT,
    // event
    LABEL_WEEK,
    LABEL_SEASON,
    LABEL_SEASON_RACE,
    LABEL_EVENT_STATUS,   // provisional/final result (only save final)
    LABEL_CAR,
    LABEL_TRACK,
    LABEL_DESC,
    LABEL_OUTFILE,
    LABEL_STATFILE,
    LABEL_SHAPE,  // par curve shape
    LABEL_GOLD_SHIFT,  // trophy curve shift
    LABEL_SQUEEZE,  // par scaling
    LABEL_SCOOT,    // zero par adjust
    LABEL_WEIGHT,   // rating weight
    LABEL_NOTE,   // WRS admin comments field
    LABEL_IMAGE,   // Images in report
    LABEL_REPORT,  // Evaluate DB for promotions
    LABEL_DB_FIX,  // Fix DB
    // submission/player
    LABEL_USER,
    LABEL_NAME,
    LABEL_PSN,
    LABEL_COUNTRY,
    LABEL_TIME,
    LABEL_TOTAL, // alias for TIME
    LABEL_SPLIT,
    LABEL_SECTOR, // alias for SPLIT
    LABEL_M3, // M3 label, for GT6 qualifier
    LABEL_MEGANE, // MEGANE label, for GT6 qualifier
    LABEL_STATUS,
    LABEL_DISQ,   // alias for LABEL_STATUS
    // player
    LABEL_PLAYER_ID, 
    LABEL_DIV,
    LABEL_SUB_DIV,
    LABEL_RATING,
    LABEL_REAL_RATING,
    LABEL_EVENT_CNT,
    LABEL_DQ_CNT,
    LABEL_VERIFIED_CNT,
    // player submodes
    LABEL_QUALIFIER,
    LABEL_HISTORY,
    // count of labels
    LABEL_ENUM_COUNT
} label_e;

typedef enum {
    STATUS_NONE, // unset
    STATUS_PROVISIONAL,
    STATUS_FINAL,
} event_status_e;

typedef enum {
    DQ_OK, // not a DQ... unchecked but assumed ok
    DQ_SUBMITTED, // not a DQ... replay submitted but not checked
    DQ_VERIFIED, // not a DQ... verified
    DQ_OFF_TRACK, // more than 2 wheels off track
    DQ_CONTACT, // racer hit wall or car
    DQ_NO_REPLAY, // racer did not provide requested replay
    DQ_TIME_ERROR, // splits do not add up to final time
    DQ_NAME_VIOLATION, // name or tag is not appropriate
    DQ_CUSTOM_VIOLATION, // custom violation, attitude, publicly revealing times, etc
} dq_reason_e;

typedef enum {
    FLAG_GREEN,
    FLAG_RED,
    FLAG_BLACK,
} flag_url_e;

typedef enum {
    ITER_DQ_ALL, // return all entries
    ITER_DQ_OK, // return only good entries
    ITER_DQ_BAD, // return only bad entries
} dq_iter_e;

/************************************************/
/* data types */

typedef struct {
    unsigned min;
    unsigned sec;
    unsigned msec;
    double time;
} ttime_t;

typedef struct _race_result {
    unsigned    race_id; // week
    unsigned    status; // provisional/final
    unsigned    points; // season points for a race
    dq_reason_e dq;
    double      rating;
    double      weight;
} race_result_t;

typedef struct _player {
    unsigned        id;             // unique ID
    unsigned        valid;
    char            name[MAX_NAME_LEN]; // GTPlanet user name
    char            psn[MAX_NAME_LEN]; // screen "GTP tag" name
    char            country[MAX_NAME_LEN]; // residence of user
    double          real_rating;
    double          rating;
    double          total_weight;
    unsigned        div;     // division 1-5
    unsigned        sub_div; // gold/silver/bronze
    unsigned        event_count;
    unsigned        dq_count; // count of DQ incidences
    unsigned        verified_count; // count of verified replays
    unsigned        history_count; // count of events in history
    race_result_t   qualifier;
    race_result_t   history[RACE_HISTORY];
    race_result_t   season[MAX_SEASON_LENGTH];
    race_result_t   latest;
} player_t;

typedef struct _player_iter {
    unsigned idx;
} player_iter_t;

typedef struct _player_link {
    player_t *player;
} player_link_t;

typedef struct _entry {
    unsigned    player_id;
    dq_reason_e dq;
    ttime_t     time;
    ttime_t     split[MAX_SPLITS];
    int         prov_div;
    int         overall_place;
    int         place;
    int         points;
    double      hcp_delta;
    double      rating;
} entry_t;

typedef struct _entry_link {
    struct _entry_link *next;
    entry_t     *entry;
} entry_link_t;

typedef struct _entry_iter {
    int div;
    dq_iter_e dq;
    entry_link_t *cur;
} entry_iter_t;

typedef struct _stat {
    unsigned count;
    ttime_t mean;
    ttime_t par; // min time for division
    ttime_t gold;
    ttime_t silver;
    ttime_t bronze; // max time for division
    double std_dev;
    ttime_t q_mean; // mean of best half (overall) or range selection
    double q_std_dev; // standard deviation of best half
    unsigned perf[3]; // <, =, > relative div count
    double hcp_delta; // average handicap delta
} stat_t;

typedef struct _event {
    int week;
    int season;
    int season_race;
    event_status_e status;
    double *par_multiple; 
    double *trophy_multiple; 
    double squeeze; 
    double scoot; 
    double weight; 
    int auto_squeeze;
    int auto_scoot;
    char car[MAX_STR_LEN];
    char track[MAX_STR_LEN];
    char description[MAX_STR_LEN];
    char outfile[MAX_STR_LEN];
    char statfile[MAX_STR_LEN];
    char img[MAX_IMAGES][MAX_STR_LEN];
    char comment[MAX_STR_LEN];
} event_t;

typedef struct _season {
    int season;
    int race_count;
    int first_event;
    int last_event;
    char season_title[MAX_STR_LEN];
    event_t event[MAX_SEASON_LENGTH];
    entry_link_t standings_link[MAX_RACERS];
    entry_link_t *standings_head[DIV_IN_USE];
} season_t;

/************************************************/
/* static tables */
unsigned g_points_table[][MAX_POINTS_PLACES+1] = {
    { 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 }, // 0 racers
    { 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0 }, // 1 racer
    { 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0 }, // 2 racers
    { 0, 7, 2, 0, 0, 0, 0, 0, 0, 0, 0 }, // 3 racers
    { 0, 8, 3, 0, 0, 0, 0, 0, 0, 0, 0 }, // 4 racers
    { 0, 9, 4, 1, 0, 0, 0, 0, 0, 0, 0 }, // 5 racers
    { 0, 9, 5, 2, 0, 0, 0, 0, 0, 0, 0 }, // 6 racers
    { 0, 9, 6, 3, 1, 0, 0, 0, 0, 0, 0 }, // 7 racers
    { 0, 9, 7, 4, 2, 0, 0, 0, 0, 0, 0 }, // 8 racers
    { 0, 9, 7, 5, 3, 1, 0, 0, 0, 0, 0 }, // 9 racers
    { 0, 10, 8, 6, 3, 1, 0, 0, 0, 0, 0 }, // 10 racers
    { 0, 10, 8, 6, 4, 2, 1, 0, 0, 0, 0 }, // 11 racers
    { 0, 10, 9, 7, 4, 3, 1, 0, 0, 0, 0 }, // 12 racers
    { 0, 10, 9, 7, 5, 4, 2, 1, 0, 0, 0 }, // 13 racers
    { 0, 10, 9, 8, 5, 4, 3, 1, 0, 0, 0 }, // 14 racers
    { 0, 10, 9, 8, 6, 5, 3, 2, 1, 0, 0 }, // 15 racers
    { 0, 10, 9, 8, 6, 5, 4, 3, 1, 0, 0 }, // 16 racers
    { 0, 10, 9, 8, 7, 6, 4, 3, 2, 1, 0 }, // 17 racers
    { 0, 10, 9, 8, 7, 6, 5, 4, 2, 1, 0 }, // 18 racers
    { 0, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1 }, // 19 racers
    { 0, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1 }, // 20+ racers
};

char g_subdiv_text[][MAX_NAME_LEN] = {
    "Gold",
    "Silver",
    "Bronze",
};

char g_color_tag[][MAX_NAME_LEN] = {
    "[COLOR=Lime]", // div 0 / rookie
    "[COLOR=Blue]",
    "[COLOR=DarkOrange]",
    "[COLOR=Magenta]",
    "[COLOR=DarkRed]",
    "[COLOR=Navy]", // div 5
    "[COLOR=Purple]", // div 6
    "[COLOR=Black]", // div 7
    "[COLOR=Black]", // div 8
};

// note: label text must match order of label enum
char g_label[][MAX_NAME_LEN] = {
    // error
    "NULL", //LABEL_NONE,
    // general
    "#", // LABEL_COMMENT
    // event
    "WEEK", //LABEL_WEEK,
    "SEASON", //LABEL_SEASON,
    "SEASON_RACE", //LABEL_SEASON_RACE,
    "EVENT_STATUS", //LABEL_EVENT_STATUS, 
    "CAR", //LABEL_CAR,
    "TRACK", //LABEL_TRACK,
    "DESC", //LABEL_DESC,
    "OUT", //LABEL_OUTFILE,
    "STATFILE", //LABEL_OUTFILE,
    "SHAPE", //LABEL_SHAPE, 
    "GOLD_SHIFT", //LABEL_GOLD_SHIFT, 
    "SQUEEZE", //LABEL_SQUEEZE, 
    "SCOOT", //LABEL_SCOOT,  
    "WEIGHT", //LABEL_WEIGHT,  
    "COMMENT", // LABEL_NOTE,
    "IMAGE",  // LABEL_IMAGE,
    "REPORT", // LABEL_REPORT,
    "DB_FIX", // LABEL_DB_FIX,
    // submission/player
    "USER", //LABEL_USER,
    "NAME", //LABEL_NAME,
    "PSN", //LABEL_PSN,
    "COUNTRY", //LABEL_COUNTRY,
    "TIME", //LABEL_TIME,
    "TOTAL", //LABEL_TOTAL,
    "SPLIT", //LABEL_SPLIT,
    "SECTOR", //LABEL_SECTOR,
    "M3", //LABEL_M3,
    "MEGANE", //LABEL_MEGANE,
    "STATUS", //LABEL_STATUS,
    "DISQ", //LABEL_DISQ,
    // player
    "PLAYER_ID", // LABEL_PLAYER_ID
    "DIV", //LABEL_DIV,
    "SUB", //LABEL_SUB_DIV,
    "RATING", //LABEL_RATING,
    "RRATING", //LABEL_REAL_RATING,
    "EVENTS", //LABEL_EVENT_CNT,
    "DQS", //LABEL_DQ_CNT,
    "VERI", //LABEL_VERIFIED_CNT,
    // player submodes
    "QUAL", // LABEL_QUALIFIER
    "HISTORY", // LABEL_HISTORY
    // count of labels
    "" //LABEL_ENUM_COUNT
};

char g_dq_text[][MAX_NAME_LEN] = {
    "OK", // DQ_OK, 
    "SUBMITTED", // DQ_SUBMITTED, "UNVERIFIED" is alias
    "VERIFIED", // DQ_VERIFIED, 
    "OFFTRACK", // DQ_OFF_TRACK, 
    "CONTACT", // DQ_CONTACT, 
    "REPLAY", // DQ_NO_REPLAY, 
    "TIMEERROR", // DQ_TIME_ERROR, 
    "NAME_VIOLATION", // DQ_NAME_VIOLATION, 
    "X", // DQ_CUSTOM_VIOLATION, 
};

char g_dq_display_text[][MAX_NAME_LEN] = {
    "", // DQ_OK, 
    "", // DQ_SUBMITTED, (Submitted), inherent in GT6
    "(Verified)", // DQ_VERIFIED, 
    "(Off Track)", // DQ_OFF_TRACK, 
    "(Contact)", // DQ_CONTACT, 
    "(No Replay)", // DQ_NO_REPLAY, 
    "(Time Error)", // DQ_TIME_ERROR, 
    "(Name Violation)", // DQ_NAME_VIOLATION, 
    "(Custom Violation)", // DQ_CUSTOM_VIOLATION, 
};

char g_replay_request_string[] = "(Replay Verify Required)";

char g_dq_flag_url[][MAX_STR_LEN] = {
    "[IMG]https://www.gtplanet.net/forum/attachments/greenflag-gif.152575/[/IMG]",
    "[IMG]https://www.gtplanet.net/forum/attachments/redflag-gif.152574/[/IMG]",
    "[IMG]https://www.gtplanet.net/forum/attachments/blackflag-gif.152573/[/IMG]",
//    "[IMG]http://users.gtpla.net/forum/attachments/greenflag-gif.152575[/IMG]",
//    "[IMG]http://users.gtpla.net/forum/attachments/redflag-gif.152574[/IMG]",
//    "[IMG]http://users.gtpla.net/forum/attachments/blackflag-gif.152573[/IMG]"
//    "[IMG]http://img42.imageshack.us/img42/5458/user118395pic1573412914.gif[/IMG]",
//    "[IMG]http://img524.imageshack.us/img524/745/rflagnv1.gif[/IMG]",
//    "[IMG]http://img249.imageshack.us/img249/5616/bflagtp3.gif[/IMG]",
};

// note: D0 is hidden, but calculated anyway
double default_par_multiple[] = { -0.5, 0.0, 1.0, 2.2, 3.5, 6.0, 8.0, 12.0, 18.0, 26.0 }; // pulled from qualifier 1
double flat_par_multiple[] = { -1.0, 0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0 }; // inc by 0.0
double standard_par_multiple[] = { -0.5, 0.0, 1.0, 2.5, 4.5, 7.0, 10.0, 13.5, 17.5, 22.0 }; // inc by 0.5
double hybrid_par_multiple[] = { -0.5, 0.0, 1.0, 2.75, 5.25, 8.5, 12.5, 17.75, 22.25, 29.0 }; // inc by 0.75
double double_par_multiple[] = { -0.5, 0.0, 1.0, 3.0, 6.0, 10.0, 15.0, 21.0, 28.0, 36.0 }; // inc by 1 over previous inc
double multiply_par_multiple[] = { -0.5, 0.0, 1.0, 3.0, 7.0, 15.0, 31.0, 63.0, 127.0, 255.0 }; // double previous inc
double custom_par_multiple[] = { -0.5, 0.0, 1.0, 2.2, 3.5, 6.0, 8.0, 12.0, 18.0, 26.0 }; // starts with default

double qual_trophy_multiple[] = { (1.0/3.0)-0.05, (2.0/3.0)-0.05, 3.0/3.0 };
double flat_trophy_multiple[] = { 1.0/3.0, 2.0/3.0, 3.0/3.0 };
double standard_trophy_multiple[] = { 0.3, (0.3 + 1.0/3.0), 1.0 };
double hybrid_trophy_multiple[] = { 0.3, (0.3 + 1.0/3.0), 1.0 };
double double_trophy_multiple[] = { 3.0/12.0, (3.0+4.0)/12.0, (3.0+4.0+5.0)/12.0 };
double multiply_trophy_multiple[] = { 3.0/12.0, (3.0+4.0)/12.0, (3.0+4.0+5.0)/12.0 };
double custom_trophy_adjust[] = { 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0 }; 

/************************************************/
char g_results_text_1[] = 
"\n[CENTER]\n[IMG]https://www.gtplanet.net/forum/data/attachments/676/676309-8d3645f5bc864e9d5790353253b364d1.jpg[/IMG]\n"
"\n[COLOR=Black][SIZE=6][B]:: GTP_Weekly Race Series ::[/B][/SIZE][/COLOR]\n\n"
"\n\n[IMG]https://www.gtplanet.net/forum/attachments/wrs-tt-main-banner-png.693509/[/IMG]\n"
"[COLOR=Black][SIZE=6][B][U]"; // week & desc
//"[IMG]https://www.gtplanet.net/forum/attachments/gran-turismo-6-b-jpg.210712/[/IMG]\n\n" // outdated

char g_results_text_2a[] = 
"[/U][/B][/SIZE][/COLOR]\n"
"[COLOR=Black][SIZE=6][B][U]Results[/U][/B][/SIZE][/COLOR]\n\n"
"[IMG]"; // img 1
char g_results_text_2b[] = 
"[/IMG]\n\n"
"[SIZE=6][COLOR=Black][B][U]Time Trial in Arcade Mode[/U][/B][/COLOR][/SIZE]\n\n"
"[IMG]"; //img 2
char g_results_text_2c[] = 
"[/IMG]\n\n[COLOR=Black][SIZE=6][U][B]"; // car

char g_results_text_3a[] = 
"[/B][/U][/SIZE][/COLOR]\n\n"
"[IMG]"; // img 3 (track logo)
char g_results_text_3b[] = 
"[/IMG]\n\n"
"[SIZE=6][COLOR=Black][B][U]"; // track

char g_results_text_4a[] =
"[/U][/B][/COLOR][/SIZE]\n"
"[/CENTER]\n\n"
"[COLOR=Black][B]Steward's Comments:[/B][/COLOR]\n"
"[COLOR=Darkblue]\n"; // comments
char g_results_text_4b[] =
"\n\nCheers,\n\nOLR Team.\n"
"[/COLOR]\n\n"
"[COLOR=Black][B]Sharing Your Replay:\n"
"[LIST]"
"[*]Go to Your Library, locate your Submitted Best Lap Replay, and share it using the in game menu features.\n"
"[*]Be sure to share your replay PUBLICLY for verification, so that any member may find it.\n"
"[*]When sharing your replay this week, please use the following share tags to make your replay easy for other members to locate\n";
char g_results_text_4c[] =
"[/LIST][/COLOR]"
"[COLOR=Darkblue]This thread will be listed as \"Provisional\" and will become \"Official\" once all posted replays have been verified.\nDisqualification isn't taken lightly within the WRS.[/COLOR]\n"
"[COLOR=Red][B]Drivers who do not have a submitted lap posted in the results are not to post any information related to a laptime they might have achieved in the results thread. Any such posts will have the times removed.[/B][/COLOR]\n\n"
"[B]\n"; // rankings

char g_results_text_5[] =
"[/B]\n\n\n"
"[COLOR=Darkblue][IMG]https://www.gtplanet.net/forum/attachments/greenflag-gif.152575/[/IMG] shows that the replay has been posted and verified.\n"
"[IMG]https://www.gtplanet.net/forum/attachments/redflag-gif.152574/[/IMG] shows that the submitted lap turned out to be dirty or doubtful.\n"
"[IMG]https://www.gtplanet.net/forum/attachments/blackflag-gif.152573/[/IMG] shows that the replay has was found to be invalid.[/COLOR]\n\n"
"[COLOR=Black][B]Replay Checking:[/B][/COLOR][COLOR=Darkblue]\n\n"
"[LIST=1]\n"
"[*]It is customary for all participants of the WRS to verify each others submitted replays\n"
"[*]Once you have checked the replay, post in this thread to say that you have checked it and whether it's clean, dirty or doesn't meet the required race specifications\n"
"[*]When verifying a replay, check against this weeks race specification, check that the tyres are the correct compound and that the power and weight is correct for example\n"
"[*]If you are unsure about a replay, always seek a second opinion before posting\n"
"[/LIST][/COLOR]\n\n";


/************************************************/
/* globals */
run_mode_e g_run_mode = RUN_MODE_EVENT;
event_t g_event;
season_t g_season;
entry_t entry_db[MAX_RACERS];
player_link_t p_sort[MAX_RACERS];
entry_link_t time_sort[MAX_RACERS];
entry_link_t rating_sort[MAX_RACERS];
entry_link_t *ov_head = 0;
entry_link_t *rat_head = 0;
player_t player_db[MAX_PLAYERS];
stat_t div_stat[DIV_COUNT+1] = {0};
stat_t ostat = {0};
unsigned g_entry_cnt = 0;
int player_cnt = -1;
int max_player_id = -1;

/************************************************/
/* functions */
int
dq_ok(dq_reason_e dq)
{
    if (dq == DQ_OK || dq == DQ_VERIFIED || dq == DQ_SUBMITTED) {
        return TRUE;
    }
    return FALSE;
}

unsigned
entry_points(entry_t *entry, unsigned racers)
{
    int idx = racers;
    unsigned points = 0;

    if (dq_ok(entry->dq)) {
        // non-DQ score at least MIN_POINTS (usually 0 or 1)
        points = MIN_POINTS;
        // only calculate points if place is within score range 
        if (entry->place <= MAX_POINTS_PLACES) {
            // cap row
            if (idx > MAX_RACER_POINTS) {
                idx = MAX_RACER_POINTS;
            }
            points = g_points_table[idx][entry->place];
            if (points < MIN_POINTS) {
                points = MIN_POINTS;
            }
        }
    }
    return points;
}

/************************************************/
// player DB interface
player_t *
player_get(unsigned id)
{ 
    if (id >= MAX_PLAYERS) { 
        id = NULL_PLAYER;
    }
    return &player_db[id];
}

player_t *
player_create(char *name, char *psn)
{
    player_t *p;
    if (max_player_id >= MAX_PLAYERS) {
        printf("max_player_id = %d; MAX_PLAYERS=%d\n", max_player_id, MAX_PLAYERS);
        return 0;
    }

    player_cnt++;
    p = &player_db[++max_player_id];
    p->id = max_player_id;
    if (p->id > 0) {
        p->valid = TRUE;
    }
    strncpy(p->name, (name ? name : "NULL"), MAX_NAME_LEN);
    strncpy(p->psn, (psn ? psn : "NULL"), MAX_NAME_LEN);
    p->real_rating = 0.0f;
    p->rating = 0.0f;
    p->total_weight = 0.0f;
    p->div = 0;     // division 1-5; 0 = rookie/unknown
    p->sub_div = SUB_DIV_GOLD; // gold/silver/bronze
    p->event_count = 0;
    p->dq_count = 0;

    return p;
}

char *
quote_strip(char *out, char *in)
{
    char *ret = out;

    while (*in) {
        if (*in == '\"') {
            in++;
        } else {
            *out++ = *in++;
        }
    }
    *out = 0;
    return ret;
}

char *
player_name(unsigned id)
{
    static char ret[MAX_NAME_LEN];

    player_t *player = player_get(id);
    quote_strip(ret, player->name);

    return ret;
}

char *
player_psn(unsigned id)
{
    player_t *player = player_get(id);
    return player->psn;
}

char *
player_country(unsigned id)
{
    static char ret[MAX_NAME_LEN];

    player_t *player = player_get(id);
    if (player->country[0]) {
        quote_strip(ret, player->country);
        return ret;
    }
    return "";
}

unsigned
player_is_rookie(unsigned id)
{
    player_t *player = player_get(id);
    if (player->qualifier.status == STATUS_FINAL ||
        ((player->total_weight >= ROOKIE_TIME) &&
         (player->verified_count >= ROOKIE_TIME))) {
        return FALSE;
    }
    return TRUE;
}

unsigned
player_div(unsigned id)
{
    player_t *player = player_get(id);
    return player->div;
}

unsigned
player_subdiv(unsigned id)
{
    player_t *player = player_get(id);
    return player->sub_div;
}

void
player_div_set(unsigned id, float rating)
{
    player_t *player = player_get(id);
    if (player->id > 0) {
        if (!player_is_rookie(player->id)) {
            player->div = (unsigned)rating;
        } else { // rookie
            player->div = 0;
        }
        if (player->div > DIV_IN_USE) {
            player->div = DIV_IN_USE;
        }
        if (rating < 1) {
            player->sub_div = SUB_DIV_GOLD;
        } else {
            player->sub_div = (unsigned)((rating - player->div)*3);
        }
        if (player->sub_div > SUB_DIV_BRONZE) {
            player->sub_div = SUB_DIV_BRONZE;
        }
    }
}

unsigned
player_rating(unsigned id)
{
    player_t *player = player_get(id);
    return player->rating;
}

void
player_update_rating(player_t *p)
{
    double agg, real_agg;
    double adj_rating;
    double use_weight;

    if (p && p->valid) {
        p->event_count++;
        if (dq_ok(p->latest.dq)) {
            use_weight = p->total_weight;
            if (use_weight >= RATING_WEIGHT_CAP) {
                use_weight = RATING_WEIGHT_CAP - p->latest.weight;
                if (use_weight <= 0) {
                    use_weight = RATING_WEIGHT_CAP;
                }
            }
            real_agg = (p->real_rating * use_weight) + (p->latest.rating * p->latest.weight);
            adj_rating = (p->latest.rating < p->rating) ? p->latest.rating : p->rating;
            agg = (p->rating * use_weight) + (adj_rating * p->latest.weight);
            use_weight += p->latest.weight;
            if (use_weight > 0.0f) {
                p->real_rating = real_agg / use_weight;
                if(NO_HARM_HANDICAP==TRUE && player_is_rookie(p->id)==FALSE) {
                    p->rating = agg / use_weight;
                } else {
                    p->rating = p->real_rating;
                }
            } else {
                p->rating = 0.0f;
            }
            if (p->latest.dq == DQ_VERIFIED)  {
                p->verified_count += p->latest.weight;
            }
            p->total_weight += p->latest.weight; // update total weight
        } else {
            p->dq_count++;
        }
        if (p->real_rating <= 0.0f) {
            p->real_rating = p->rating;
        } else if (p->rating <= 0.0f) {
            p->rating = p->real_rating;
        }
    }
}

player_t *
player_lookup_by_psn(char *psn)
{
    int i;
    if (!psn || !psn[0]) {
        return 0;
    }
    for (i = 1; i <= max_player_id; i++) {
        if (!strcmp(psn, player_db[i].psn)) {
            return &player_db[i];
        }
    }
    return 0;
}

player_t *
player_lookup_by_name(char *name)
{
    int i;
    if (!name || !name[0]) {
        return 0;
    }
    for (i = 0; i < max_player_id; i++) {
        if (!strcmp(name, player_db[i+1].name)) {
            return &player_db[i+1];
        }
    }
    return 0;
}

player_t *
player_get_next(player_iter_t *iter)
{
    player_t *p;
    do {
        iter->idx++;
        p = player_get(iter->idx);
    } while (iter->idx <= max_player_id && p->valid != TRUE);
    if (iter->idx > max_player_id) {
        return 0;
    }
    return p;
}

player_t *
player_get_first(player_iter_t *iter)
{
    iter->idx = 0;
    return player_get_next(iter);
}

/************************************************/
// race entry API

entry_t *
entry_find(entry_t *entry)
{
    int i;
    for (i = 0; i < g_entry_cnt; i++) {
        if (entry->player_id == entry_db[i].player_id) {
            return &entry_db[i];
        }
    }
    return 0;
}

char *
entry_name(entry_t *entry)
{
    if (entry) {
        return player_name(entry->player_id);
    }
    return 0;
}

char *
entry_psn(entry_t *entry)
{
    if (entry) {
        return player_psn(entry->player_id);
    }
    return 0;
}

char
entry_rookie(entry_t *entry)
{
    char retval = '-';
    if (entry && player_is_rookie(entry->player_id)) {
        retval = 'R';
    }
    return retval;
}

unsigned
entry_div(entry_t *entry)
{
    unsigned retval = 0;
    if (entry) {
        retval =  player_div(entry->player_id);
        if (!retval) {
            retval = entry->prov_div;
        }
    }
    return retval;
}

unsigned
entry_subdiv(entry_t *entry)
{
    unsigned retval = 0;
    if (entry) {
        retval =  player_subdiv(entry->player_id);
    }
    return retval;
}

int
entry_watch(entry_t *e)
{
    if (e->rating*3.0f < (entry_div(e)*3.0f + entry_subdiv(e))) {
        return TRUE;
    }
    return FALSE;
}

int
entry_struggle(entry_t *e)
{
    if (entry_div(e) >= DIV_IN_USE-1) {
        return FALSE;
    }
    if (e->prov_div > entry_div(e) && e->hcp_delta > (SUB_DIVISION_RANGE*2.0f)) {
        return TRUE;
    }
    return FALSE;
}

int 
entry_need_replay(entry_t *e)
{
    if (g_event.status != STATUS_FINAL &&
        ((e->place <= 3) ||
         (player_is_rookie(e->player_id)) ||
         (e->hcp_delta < -(SUB_DIVISION_RANGE)) ) ) {
        return TRUE;
    }
    return FALSE;
}

char *
entry_replay_string(entry_t *e)
{
    char *retval = "";
    if (e->dq >= DQ_VERIFIED) {
        retval =  g_dq_display_text[e->dq];
    } else if (entry_need_replay(e)) {
        retval =  g_replay_request_string;
    }
    return retval;
}

char *
entry_dq_flag(entry_t *e)
{
    char *retval = "";
    if (e->dq == DQ_VERIFIED) {
        retval = g_dq_flag_url[FLAG_GREEN];
    } else if (e->dq >= DQ_NO_REPLAY) {
        retval = g_dq_flag_url[FLAG_BLACK];
    } else if (e->dq >= DQ_OFF_TRACK) {
        retval = g_dq_flag_url[FLAG_RED];
    }
    return retval;
}

int
entry_dq_match(dq_reason_e status, dq_iter_e query)
{
    if (query == ITER_DQ_ALL) {
        return TRUE;
    } else if (query == ITER_DQ_OK) {
        return dq_ok(status);
    } else {
        return !dq_ok(status);
    }
}

unsigned
entry_match(entry_iter_t *iter)
{
    if (!iter->cur || !iter->cur->entry) {
        return FALSE;
    }
    if (((iter->div == DIV_ALL) ||
         (entry_div(iter->cur->entry) == iter->div)) &&
            entry_dq_match(iter->cur->entry->dq, iter->dq)) {
        return TRUE;
    }
    return FALSE;
}

entry_t *
entry_get_next(entry_iter_t *iter)
{
    do {
        iter->cur = iter->cur->next;
    } while (iter->cur && !entry_match(iter));
    return (iter->cur ? iter->cur->entry : 0);
}

entry_t *
entry_get_first(entry_iter_t *iter, entry_link_t *head, int div, dq_iter_e dq)
{
    iter->div = div;
    iter->dq = dq;
    iter->cur = head;
    if (iter->cur && !entry_match(iter)) {
        entry_get_next(iter);
    }
    return (iter->cur ? iter->cur->entry : 0);
}

int comparisons = 0;
int
player_compare(const void *a, const void *b)
{
comparisons++;
    player_link_t *left = (player_link_t *)a;
    player_link_t *right = (player_link_t *)b;
    if (left->player->rating < right->player->rating) {
        -1;
    } else if (left->player->rating > right->player->rating) {
        1;
    }
    return 0;
}

void
bsort(player_link_t *base, size_t num, size_t size, int (*compare)(const void*, const void*))
{
    int i, j;
    player_t *tmp;
    for (i = 0; i < num; i++) {
        for (j = i+1; j < num; j++) {
            if (base[i].player->rating > base[j].player->rating) {
comparisons++;
                tmp = base[i].player;
                base[i].player = base[j].player;
                base[j].player = tmp;
            }
        }
    }
}

player_link_t *
player_sort(int div, sub_div_e sub)
{
    player_t *player;
    int p = 0;
    int i;
    for (i = 0; i <= player_cnt; i++) {
        p_sort[i].player = 0;
    }
    for (i = 1; i <= player_cnt; i++) {
        player = &player_db[i];
        if (player->div == div && player->sub_div == sub) {
            p_sort[p++].player = player;
        }
    }
    if (p > 1) {
//        qsort(p_sort, p, sizeof(player_link_t), player_compare);
        bsort(p_sort, p, sizeof(player_link_t), player_compare);
        printf("D%d qsort: %d elements, %d comparisons\n", div, p, comparisons);
        comparisons = 0;
    }
    return p_sort;
}

/************************************************/
// event entry API
int
event_season_active()
{
    if (g_event.season) {
        return TRUE;
    } else {
        return FALSE;
    }
}

int
event_season()
{
    return g_event.season;
}

int
event_season_race()
{
    return g_event.season_race;
}

/************************************************/
// init
void
init_db()
{
    int i;

    g_entry_cnt = 0;

    // init event
    memset(&g_event, 0, sizeof(event_t));
    g_event.par_multiple = flat_par_multiple;
    g_event.trophy_multiple = qual_trophy_multiple;
    g_event.squeeze = DEFAULT_SQUEEZE;
    g_event.scoot = DEFAULT_SCOOT;
    g_event.weight = 1.0f;
    g_event.auto_squeeze = TRUE;
    g_event.auto_scoot = TRUE;
    strcpy(g_event.comment, "Good job everyone!");

    for (i = 0; i < MAX_PLAYERS; i++) {
        memset(&player_db[i], 0, sizeof(player_t));
    }
    player_create("NULL", "NULL"); // add player 0
    for (i = 0; i < MAX_RACERS; i++) {
        memset(&entry_db[i], 0, sizeof(entry_t));
    }
    ov_head = 0;
    rat_head = 0;
    for (i = 0; i <= DIV_COUNT; i++) {
        memset(&div_stat[i], 0, sizeof(stat_t));
        custom_trophy_adjust[i] = 0.0;
        custom_par_multiple[i] = default_par_multiple[i];
    }
    memset(&ostat, 0, sizeof(stat_t));
}

/************************************************/
// generic file scanner...
int
scan_to(FILE *file, char *string, int max_lines)
{
    char cur_line[MAX_LINE_LEN];
    int len = strlen(string);
    while (!feof(file) && ((max_lines--) > 0)) {
        if (fgets(cur_line, MAX_LINE_LEN-1, file) == 0) {
            continue;
        }
        if (!strncmp(cur_line, string, len)) {
            return SUCCESS;
        }
    }
    // may want to rewind in fail case
    fprintf(stderr, "scan_to(%s), len=%d not found\n", string, len);
    return FAILURE;
}

int
label_end(char c)
{
    if (c == ':') {
//    if (c == ' ') {
        return TRUE;
    }
    return FALSE;
}

int
label_len(char *str)
{
    int len = 0;

    if (!str) {
        return 0;
    }
    while (*str && !label_end(*str) && (len < MAX_STR_LEN)) {
        len++;
        str++;
    }
    len++; // skip past label end
    return len;
}

char *
label_skip(char *str)
{
    int len = 0;

    if (!str) {
        return 0;
    }
    len = label_len(str);
    str += len;
    // skip past space following label
    while (isspace(*str) && len < MAX_STR_LEN) {
        len++;
        str++;
    }
    return str;
}

int
label_copy_toupper(char *out, char *in)
{
    int len = 0;
    // skip past leading spaces
    while (isspace(*in) && len < MAX_STR_LEN) {
        in++;
        len++;
    }
    // copy label
    while (!isspace(*in) && len < MAX_STR_LEN) {
        len++;
        *out++ = toupper(*in++);
    }
    // null terminate copy
    *out = 0;
    return len;
}

// label_get
// input: string: pointer to string to search for label
// returns: id of string found, or LABEL_NONE
label_e
label_get(char *string)
{
    label_e label;
    size_t offset;
    char copy[MAX_STR_LEN];

    if (!string) {
        return LABEL_NONE;
    }
    offset = label_copy_toupper(copy, string);
    if (offset == 0) {
        return LABEL_NONE;
    }

    for (label = LABEL_COMMENT; label < LABEL_ENUM_COUNT; label++) {
        if (!strncmp(copy, g_label[label], strlen(g_label[label]))) {
            // found label
            return label;
        }
    }
    return LABEL_NONE;
}

int
string_copy(char *out, char *in)
{
    int len = 0;
    if (out && in) {
        while (isprint(*in) && len < MAX_STR_LEN) {
            *out++ = *in++;
            len++;
        }
        *out = 0;
    }
    return len;
}

int
field_len(char *str)
{
    int len = 0;

    if (!str) {
        return 0;
    }
    if (*str == '\"') {
        len++;
        str++;
        while (*str && (*str != '\"') && len < MAX_STR_LEN) { 
            len++;
            str++;
        }
        if (len < MAX_STR_LEN) {
            len++;
        }
    } else {
        while (*str && !isspace(*str) && len < MAX_STR_LEN) {
            len++;
            str++;
        }
    }
    return len;
}

char *
field_copy(char *dst, char *src) {
    // strip quotes
    int len = field_len(src);
    if (len < 2 && (len == 0 || *src == '\"')) {
        return 0;
    }
    int offset = 0;
    if (*src == '\"') {
        offset = 1;
    }
    strncpy(dst, src+offset, len-(2*offset));
    dst[len-(2*offset)] = 0;
    return dst + len;
}

char *
field_skip(char *str)
{
    int len = 0;

    if (!str) {
        return 0;
    }
    len = field_len(str);
    str += len;

    // skip past space following field
    while (isspace(*str) && len < MAX_STR_LEN) {
        len++;
        str++;
    }
    return str;
}

int
parse_time(char *str, ttime_t *time)
{
    if (!str || !time) {
        return FAILURE;
    }
    time->min = atoi(str);
    while (isdigit(*str)) str++;
    while (*str && !isdigit(*str)) str++;
    time->sec = atoi(str);
    while (isdigit(*str)) str++;
    if (isspace(*str)) {
        // sec.msec format
        time->msec = time->sec;
        time->sec = time->min;
        time->min = 0;
    } else {
        while (*str && !isdigit(*str)) str++;
        time->msec = atoi(str);
    }
    while (time->sec > 60) {
        time->min++;
        time->sec -= 60;
    }
    return SUCCESS;
}

/************************************************/
// time functions
int
time_to_usec(ttime_t *t)
{
    return (t->min * 60 * 1000) + (t->sec * 1000) + t->msec;
}

void
time_from_usec(ttime_t *t, int usec)
{
    if (t) {
        t->time = (double)usec/1000.0;
        t->min = usec / (60 * 1000);
        usec -= t->min * 60 * 1000;
        t->sec = usec / 1000;
        t->msec = usec - (t->sec * 1000);
    }
}

int
time_compare(entry_t *left, entry_t *right)
{
    return time_to_usec(&left->time) - time_to_usec(&right->time);
}

void
time_add(ttime_t *dest, ttime_t *a, ttime_t *b)
{
    int usec;
    if (dest && a && b) {
        usec = time_to_usec(a) + time_to_usec(b);
        time_from_usec(dest, usec);
    }
}

void
time_subtract(ttime_t *dest, ttime_t *a, ttime_t *b)
{
    int usec;
    if (dest && a && b) {
        usec = time_to_usec(a) - time_to_usec(b);
        time_from_usec(dest, usec);
    }
}

char *
time_display(ttime_t *time)
{
    static char sbuf[MAX_NAME_LEN];
    sprintf(sbuf, "%u'%2.2u.%3.3u", (unsigned char)time->min, (unsigned char)time->sec, (unsigned short)time->msec);
    return sbuf;
}

entry_link_t *
time_insert(entry_link_t *head, entry_link_t *link, entry_t *entry)
{
    entry_link_t *prev, *cur;

    link->entry = entry;
    prev = 0;
    cur = head;
    while (cur && time_compare(cur->entry, entry) < 0) {
        prev = cur;
        cur = cur->next;
    }
    if (prev == 0) { // new head
        head = link;
    } else {
        prev->next = link;
    }
    link->next = cur;
    return head; // return new head
}

double
weight_adjust(double player_rating, double event_rating)
{
    double delta = event_rating - player_rating;

    if (player_rating <= 0.0f || delta < 1.0f) {
        delta = 1.0f;
    }
    return (1.0f/2.0f + 1.0f/(2.0f*delta));
}

void
time_rate(entry_t *e)
{
    player_t *player;
    double base, range;
    stat_t *div;
    unsigned subdiv;

    div = &div_stat[e->prov_div];
    e->rating = 3.0*(e->prov_div);
    if (time_to_usec(&e->time) < time_to_usec(&div->gold)) {
        subdiv = SUB_DIV_GOLD;
        base = div->par.time;
        range = div->gold.time - base;
    } else if (time_to_usec(&e->time) < time_to_usec(&div->silver)) {
        subdiv = SUB_DIV_SILVER;
        base = div->gold.time;
        range = div->silver.time - base;
        e->rating += 1.0;
    } else { // bronze
        subdiv = SUB_DIV_BRONZE;
        base = div->silver.time;
        range = div->bronze.time - base;
        e->rating += 2.0;
    }
    if (range > 0) {
        e->rating += (e->time.time - base) / range;
    }
    // normalize
    e->rating = e->rating/3.0f;
    // cap at max
    if (e->rating > (DIV_IN_USE+1)) {
        e->rating = (float)(DIV_IN_USE+1)-0.001;
    }

    // compare against handicap
    e->hcp_delta = 0.0f;
    player = player_get(e->player_id);
    if (player && player->rating > 0.0f) {
        if (player->div > 0) {
            div = &div_stat[entry_div(e)];
        }
        // low numbers indicate underperform
        e->hcp_delta = (e->rating - player->rating);
//        e->hcp_delta = 3.0f*(e->rating - div) - player->sub_div - 0.5f;
        if (e->hcp_delta <= -(SUB_DIVISION_RANGE*0.5f)) { 
            div->perf[0]++; 
        } else if (e->hcp_delta >= (SUB_DIVISION_RANGE*0.5f)) {
            div->perf[2]++; 
        } else {
            div->perf[1]++; 
        }
    } else if (g_event.week == EVENT_QUALIFIER) {
        // for qualifier, track division distribution
        div = &div_stat[e->prov_div];
        div->perf[subdiv]++;
    }
}

// returns the handicap (in usec) of the entry passed in.
int
time_handicap(entry_t *e)
{
    double usec;
    player_t *player;

    player = player_get(e->player_id);
    if (!player) {
        return 0; 
    }
    double base = time_to_usec(&div_stat[1].gold);
    double mid = time_to_usec(&div_stat[3].gold);
    double handicap = (e->rating - player->rating);
    usec = mid + ((mid - base) * handicap);

    return usec;
}

char *
rating_delta_display(entry_t *e)
{
    static char sbuf[MAX_NAME_LEN];
    player_t *player;

    player = player_get(e->player_id);
    if (!player || player_is_rookie(e->player_id)) {
        sbuf[0] = 0;
    } else {
        sprintf(sbuf, "%.5f", e->rating - player->rating);
    }

    return sbuf;
}

double
rating_compare(entry_t *left, entry_t *right)
{
    player_t *left_player, *right_player;
    double left_delta, right_delta;

    left_player = player_get(left->player_id);
    right_player = player_get(right->player_id);
    if (!left_player || !right_player) {
        return 0;
    }
    left_delta = left->rating - left_player->rating;
    right_delta = right->rating - right_player->rating;
    return left_delta - right_delta;
}

entry_link_t *
rating_insert(entry_link_t *head, entry_link_t *link, entry_t *entry)
{
    entry_link_t *prev, *cur;

    link->entry = entry;
    prev = 0;
    cur = head;
    while (cur && rating_compare(cur->entry, entry) < 0) {
        prev = cur;
        cur = cur->next;
    }
    if (prev == 0) { // new head
        head = link;
    } else {
        prev->next = link;
    }
    link->next = cur;
    return head; // return new head
}

void
sort_ratings(void)
{
    int i;
    entry_t *cur;
    entry_iter_t iter;

    for (i=0, cur = entry_get_first(&iter, ov_head, DIV_ALL, ITER_DQ_OK);
            cur; i++, cur = entry_get_next(&iter)) {
        rat_head = rating_insert(rat_head, &rating_sort[i], cur);
// obsolete
//        if (player_div(cur->player_id) == 0) {
//            player_div_set(cur->player_id, cur->rating);
//        }
    }

}

void
calculate_par(void)
{
    int div, q_count;
    entry_t *cur;
    entry_iter_t iter;
    stat_t *stat;
    double base_time, par_inc, span, parXlo, parXhi;

    base_time = (((double)time_to_usec(&ostat.q_mean))/1000.0 - (ostat.q_std_dev*2.0)) + g_event.scoot;
    par_inc = ostat.q_std_dev * g_event.squeeze;
    for (div = 1; div <= DIV_COUNT; div++) {
        parXlo = g_event.par_multiple[div];
        parXhi = g_event.par_multiple[div+1];
        if (div >= DIV_IN_USE) {
            parXlo += ((float)DIV_IN_USE)*(div-DIV_IN_USE);
        }
        if (div+1 >= DIV_IN_USE) {
            parXhi += ((float)DIV_IN_USE)*(div+1-DIV_IN_USE);
        } 
        stat = &div_stat[div];
//        stat->par.time = base_time + (par_inc * g_event.par_multiple[div]);
        stat->par.time = base_time + (par_inc * parXlo);
        stat->perf[0] = 0;
        stat->perf[1] = 0;
        stat->perf[2] = 0;
        time_from_usec(&stat->par, stat->par.time*1000.0);
        stat->bronze.time = base_time + (par_inc * parXhi) - 0.001;
        span = stat->bronze.time - stat->par.time;
        stat->gold.time = stat->par.time + (span * (g_event.trophy_multiple[0]+custom_trophy_adjust[div]));
        stat->silver.time = stat->par.time + (span * (g_event.trophy_multiple[1]+custom_trophy_adjust[div]));
        time_from_usec(&stat->gold, stat->gold.time*1000.0);
        time_from_usec(&stat->silver, stat->silver.time*1000.0);
        time_from_usec(&stat->bronze, stat->bronze.time*1000.0);
    }

    // quality stats for division
    q_count = 0;
    div = 1;
    stat = &div_stat[div];
    stat->q_mean.msec = 0;
    for (cur = entry_get_first(&iter, ov_head, DIV_ALL, ITER_DQ_OK); ; cur = entry_get_next(&iter)) {
        if (!cur || (time_to_usec(&cur->time) >= time_to_usec(&stat->bronze))) {
            // close off current division
            stat->q_mean.msec += q_count/2;
            stat->q_mean.msec = (q_count ? stat->q_mean.msec/q_count : 0);
            time_from_usec(&stat->q_mean, stat->q_mean.msec);
            // advance division pointer
            q_count = 0;
            div++;
            stat = &div_stat[div];
            // end of list condition
            if (!cur || div >= DIV_COUNT) {
                break;
            }
            stat->q_mean.msec = 0;
        }
        cur->prov_div = div;
        q_count++;
        stat->q_mean.msec += time_to_usec(&cur->time);
    }
    div = 1;
    q_count = 0;
    stat = &div_stat[div];
    stat->q_std_dev = 0;
    for (cur = entry_get_first(&iter, ov_head, DIV_ALL, ITER_DQ_OK); ; cur = entry_get_next(&iter)) {
        if (!cur || cur->prov_div == div+2) {
            // close off division std deviation
            if (q_count > 0) {
                stat->q_std_dev = stat->q_std_dev / (double)q_count;
                stat->q_std_dev = sqrt(stat->q_std_dev);
            } else {
                stat->q_std_dev = 0.0f;
            }
            // advance division 
            q_count = 0;
            div++;
            stat = &div_stat[div];
            // end of list condition
            if (!cur || div >= DIV_COUNT) {
                break;
            }
            stat->q_std_dev = 0;
        }
        q_count++;
        stat->q_std_dev += (stat->q_mean.time - cur->time.time) *
                           (stat->q_mean.time - cur->time.time);
    }
}

void
rate_times(void)
{
    int div, i, prior_place;
    entry_t *cur, *prior;
    entry_iter_t iter;
    stat_t *stat;

    prior = 0;
    for (i=1, cur = entry_get_first(&iter, ov_head, DIV_ALL, ITER_DQ_OK);
            cur; i++, cur = entry_get_next(&iter)) {
        time_rate(cur);
        if (prior && !time_compare(cur, prior)) {
            cur->overall_place = prior_place;
        } else {
            cur->overall_place = i;
            prior = cur;
            prior_place = i;
        }
    }

    // finalize division stats
    for (div = 1; div <= DIV_COUNT; div++) {
        stat = &div_stat[div];
//        memset(stat, 0, sizeof(stat_t));
        stat->count = 0;
        stat->mean.msec = 0;
        stat->hcp_delta = 0;
        stat->std_dev = 0;

        // first, compute mean (average)
        for (cur = entry_get_first(&iter, ov_head, div, ITER_DQ_OK); cur; cur = entry_get_next(&iter)) {
            stat->count++;
            stat->mean.msec += time_to_usec(&cur->time);
            stat->hcp_delta += cur->hcp_delta;
            cur->time.time = (double)(time_to_usec(&cur->time))/1000.0;
        }
        if (stat->count == 0) {
            continue;
        }
        stat->mean.msec += stat->count/2; // for rounding
        stat->mean.msec = stat->mean.msec / stat->count;
        time_from_usec(&stat->mean, stat->mean.msec);
        ostat.hcp_delta += stat->hcp_delta;
        stat->hcp_delta = stat->hcp_delta / stat->count;

        // next, compute standard deviation
        for (cur = entry_get_first(&iter, ov_head, div, ITER_DQ_OK); cur; cur = entry_get_next(&iter)) {
            stat->std_dev += (stat->mean.time - cur->time.time) *
                             (stat->mean.time - cur->time.time);
        }
        stat->std_dev = stat->std_dev / (double)stat->count;
        stat->std_dev = sqrt(stat->std_dev);

        // assign place/points
        cur = entry_get_first(&iter, ov_head, div, ITER_DQ_OK);
        prior = 0;
        for (i = 1; cur; i++, cur = entry_get_next(&iter)) {
            if (prior && !time_compare(cur, prior)) {
                cur->place = prior_place;
            } else {
                cur->place = i;
                prior = cur;
                prior_place = i;
            }
            cur->points = entry_points(cur, stat->count);
        }
    }
    ostat.hcp_delta = ostat.hcp_delta / ostat.count;
}

double
calculate_auto_scoot(void)
{
    int i, hcp, div;
    double accum, usec;
    entry_t *cur;
    entry_iter_t iter;

    hcp = 0;
    accum = 0;
    // calculate the average handicap of the top division
    div = 1;
    if (div_stat[div].count < 3) {
        div = DIV_ALL;
    }
    for (i = 0, cur = entry_get_first(&iter, ov_head, div, ITER_DQ_OK);
            cur && i < (ostat.count/AUTO_SCOOT_FRACTION);
            i++, cur = entry_get_next(&iter)) {
        usec = (player_get(cur->player_id)->rating - cur->rating);
        usec *= g_event.par_multiple[2];
        usec *= ostat.q_std_dev;

        accum += usec*0.75;
    }
    if (i > 0) {
        accum = accum / i;
    }
    accum = g_event.scoot - accum;

    return accum;
}

double
calculate_auto_squeeze(void)
{
    int div;
    double accum;
    stat_t *stat;

    accum = 0;
    for (div = 1; div <= DIV_IN_USE; div++) {
        stat = &div_stat[div];
        accum += stat->count * stat->hcp_delta; 
    }
    if (ostat.count > 0) {
        accum = accum / ostat.count;
    }
    accum += g_event.squeeze;

    return accum;
}

void
collate_stats(void)
{
    int i, q_count;
    entry_t *cur;
    entry_iter_t iter;

    if (g_entry_cnt == 0) {
        fprintf(stderr, "collate_stats: no entries found\n");
        return;
    }
    // overall stats
    ostat.count = 0;
    for (cur = entry_get_first(&iter, ov_head, DIV_ALL, ITER_DQ_OK); cur; cur = entry_get_next(&iter)) {
        ostat.count++;
        ostat.mean.msec += time_to_usec(&cur->time);
        cur->time.time = (double)(time_to_usec(&cur->time))/1000.0;
    }
    if (ostat.count == 0) {
        fprintf(stderr, "collate_stats: no valid entries found\n");
        return;
    }
    ostat.mean.msec += ostat.count/2; // for rounding
    ostat.mean.msec = ostat.mean.msec / ostat.count;
    time_from_usec(&ostat.mean, ostat.mean.msec);

    q_count = 0;
    for (cur = entry_get_first(&iter, ov_head, DIV_ALL, ITER_DQ_OK); cur; cur = entry_get_next(&iter)) {
        ostat.std_dev += (ostat.mean.time - cur->time.time) *
                         (ostat.mean.time - cur->time.time);
        // compute quality time stats
        if (time_to_usec(&cur->time) <= time_to_usec(&ostat.mean)) {
            q_count++;
            ostat.q_mean.msec += time_to_usec(&cur->time);
        }
    }
    ostat.std_dev = ostat.std_dev / (double)ostat.count;
    ostat.std_dev = sqrt(ostat.std_dev);

    // finish quality stats calculation
    ostat.q_mean.msec += q_count/2; // for rounding
    if (q_count > 0) {
        ostat.q_mean.msec = ostat.q_mean.msec / q_count;
    } else {
        ostat.q_mean.msec = 0;
    }
    time_from_usec(&ostat.q_mean, ostat.q_mean.msec);
    for (cur = entry_get_first(&iter, ov_head, DIV_ALL, ITER_DQ_OK); cur; cur = entry_get_next(&iter)) {
        if (time_to_usec(&cur->time) <= time_to_usec(&ostat.mean)) {
            ostat.q_std_dev += (ostat.q_mean.time - cur->time.time) *
                               (ostat.q_mean.time - cur->time.time);
        }
    }
    if (q_count) {
        ostat.q_std_dev = ostat.q_std_dev / (double)q_count;
    } else {
        ostat.q_std_dev = 0;
    }
    ostat.q_std_dev = sqrt(ostat.q_std_dev);

    calculate_par();
    rate_times();

    // do a few iterations of this
    if (g_event.auto_scoot == TRUE || g_event.auto_squeeze == TRUE) {
        for (i = 0; i < AUTO_CYCLE_CNT; i++) {
            if (g_event.auto_scoot == TRUE && i < AUTO_CYCLE_CNT-2) {
                g_event.scoot = calculate_auto_scoot();
                calculate_par();
                rate_times();
            }
            if (g_event.auto_squeeze == TRUE) {
                g_event.squeeze = calculate_auto_squeeze();
                calculate_par();
                rate_times();
            }
            fprintf(stderr, "temp auto adjust: scoot=%.3f, squeeze=%.3f\n", g_event.scoot, g_event.squeeze);
        }
        if (g_event.auto_scoot == TRUE) {
            fprintf(stderr, "scoot auto adjust to %.3f\n", g_event.scoot);
        }
        if (g_event.auto_squeeze == TRUE) {
            fprintf(stderr, "squeeze auto adjust to %.3f\n", g_event.squeeze);
        }
    }
    sort_ratings();
}


/************************************************/
/* parser                                       */
/************************************************/
void
add_splits(entry_t *e)
{
    int i;

    memset(&e->time, 0, sizeof(ttime_t));
    for (i = 0; i < MAX_SPLITS; i++) {
        time_add(&e->time, &e->time, &e->split[i]);
    }
}

void
check_splits(entry_t *e)
{
    int i;
    ttime_t accum;

    memset(&accum, 0, sizeof(ttime_t));
    for (i = 0; i < MAX_SPLITS; i++) {
        time_add(&accum, &accum, &e->split[i]);
    }
    if (time_to_usec(&accum) &&
            time_to_usec(&e->time) != time_to_usec(&accum)) {
        fprintf(stderr, "Split addition error for %s: Time=(%s), ",
                entry_psn(e), time_display(&e->time));
        fprintf(stderr, "Splits=(%s)\n", time_display(&accum));
        e->dq = DQ_TIME_ERROR;
    }
}

void
parse_custom_curve_shape(char *ptr)
{
    int i = 0;
    ptr = field_skip(ptr);
    while (*ptr) {
        if ((*ptr == '-' || *ptr == '.' || isdigit(*ptr)) && i <= DIV_COUNT) {
            custom_par_multiple[i] = atof(ptr);
            i++;
        }
        ptr = field_skip(ptr);
    }
    printf("Custom par: ");
    for (i = 0; i < DIV_COUNT; i++) {
        printf("%.3f ", custom_par_multiple[i]);
    }
    printf("\n");
}

void
parse_custom_gold_shift(char *ptr)
{
    int i = 0;
    double val;

    while (*ptr) {
        if ((*ptr == '-' || *ptr == '.' || isdigit(*ptr)) && i <= DIV_COUNT) {
            val = atof(ptr);
            if (val > -2.0/3.0 && val < 2.0/3.0) { // allowable range
                custom_trophy_adjust[i] = atof(ptr);
                i++;
            } else {
                printf("Gold Trophy Shift range error: %.3f should be from -2/3 and 2/3\n", val);
            }
        }
        ptr = field_skip(ptr);
    }
    printf("Gold Trophy Shift: ");
    for (i = 0; i <= DIV_COUNT; i++) {
        printf("%.3f ", custom_trophy_adjust[i]);
    }
    printf("\n");
}

// Returns: count of tokens processed
int
event_process_line(char *line, entry_t *entry)
{
    int retval = 0;
    label_e label;
    player_t *player = 0;
    ttime_t time;
    entry_t *prior_entry;
    char buf[MAX_STR_LEN];
    int len, i;
    int got_entry = FALSE;
    char *ptr = line;
    char *pptr;
    do {
        time_from_usec(&time, 0);
        pptr = ptr;
        label = label_get(ptr);
        ptr = label_skip(ptr); // skip label
        retval++;
        switch(label) {
        case LABEL_COMMENT:
            label = LABEL_NONE;
            retval--; // skip rest of line
            break;
        case LABEL_NAME:
        case LABEL_PSN:
            field_copy(buf, ptr);
            if (!player) {
                player = player_lookup_by_psn(buf);
            }
            if (player) {
                strcpy(player->psn, buf);
            } else if (g_event.week == EVENT_QUALIFIER) {
                player = player_create(0, buf);
                if (!player) {
                    fprintf(stderr, "max player count exceeded\n");
                    return FAILURE;
                }
            } else {
                fprintf(stderr, "racer '%s' not registered\n", buf);
                return FAILURE;
            }
#if 0 // no name enforcement (GT6)
            label_copy_toupper(buf, player->psn);
            if (strncmp(buf, GTP_TAG, strlen(GTP_TAG))) {
                fprintf(stderr, "GTP Tag name violation for %s\n", player->psn);
                entry->dq = DQ_NAME_VIOLATION;
            }
#endif
            break;
        case LABEL_USER:
            field_copy(buf, ptr);
            if (!player) {
                player = player_lookup_by_name(buf);
            }
            if (player) {
                strcpy(player->name, buf);
            } else if (g_event.week == EVENT_QUALIFIER) {
                player = player_create(buf, 0);
                if (!player) {
                    fprintf(stderr, "max player count exceeded\n");
                    return FAILURE;
                }
            } else {
                fprintf(stderr, "racer '%s' not registered\n", buf);
                return FAILURE;
            }
            break;
        case LABEL_COUNTRY:
            if (player) {
                field_copy(player->country, ptr);
            }
            break;
        case LABEL_TIME:
        case LABEL_TOTAL:
            parse_time(ptr, &entry->time);
            got_entry = TRUE;
            break;
        case LABEL_SPLIT:
        case LABEL_SECTOR:
        case LABEL_M3:
        case LABEL_MEGANE:
            for (i = 0; i < MAX_SPLITS; i++) {
                if (time_to_usec(&entry->split[i]) == 0) {
                    parse_time(ptr, &entry->split[i]);
                    got_entry = TRUE;
                    break; // for
                }
            }
            break;
        case LABEL_STATUS:
        case LABEL_DISQ:
            if (toupper(*ptr) == 'O') {
                entry->dq = DQ_OFF_TRACK;
            } else if (toupper(*ptr) == 'C') {
                entry->dq = DQ_CONTACT;
            } else if (toupper(*ptr) == 'R') {
                entry->dq = DQ_NO_REPLAY;
            } else if (toupper(*ptr) == 'T') {
                entry->dq = DQ_TIME_ERROR;
            } else if (toupper(*ptr) == 'N') {
                entry->dq = DQ_NAME_VIOLATION;
            } else if (toupper(*ptr) == 'X') {
                entry->dq = DQ_CUSTOM_VIOLATION;
            } else if ((toupper(*ptr) == 'S') || (toupper(*ptr) == 'U')) { // unchecked
                entry->dq = DQ_SUBMITTED;
            } else if (toupper(*ptr) == 'V' || toupper(*ptr) == 'G') {
                entry->dq = DQ_VERIFIED;
            } else {
                entry->dq = DQ_OK;
            }
            break;
        case LABEL_WEEK:
            g_event.week = atoi(ptr);
            break;
        case LABEL_SEASON:
            g_event.season = atoi(ptr);
            break;
        case LABEL_SEASON_RACE:
            g_event.season_race = atoi(ptr);
            break;
        case LABEL_EVENT_STATUS:
            if (toupper(*ptr) == 'F') {
                g_event.status = STATUS_FINAL;
            } else if (toupper(*ptr) == 'P') {
                g_event.status = STATUS_PROVISIONAL;
            } else {
                fprintf(stderr, "Unknown status: '%s'\n", ptr);
            }
            break;
        case LABEL_CAR:
            string_copy(g_event.car, ptr); // to end of line
            g_event.car[strlen(ptr)] = 0;
            return retval;
            break;
        case LABEL_TRACK:
            string_copy(g_event.track, ptr); // to end of line
            g_event.track[strlen(ptr)] = 0;
            return retval;
            break;
        case LABEL_DESC:
            string_copy(g_event.description, ptr); // to end of line
            g_event.description[strlen(ptr)] = 0;
            return retval;
            break;
        case LABEL_OUTFILE:
            string_copy(g_event.outfile, ptr); // to end of line
            g_event.outfile[strlen(ptr)] = 0;
            return retval;
            break;
        case LABEL_STATFILE:
            string_copy(g_event.statfile, ptr); // to end of line
            g_event.statfile[strlen(ptr)] = 0;
            return retval;
            break;
        case LABEL_NOTE:
            string_copy(g_event.comment, ptr); // to end of line
            g_event.comment[strlen(ptr)] = 0;
            return retval;
            break;
        case LABEL_IMAGE:
            for (i = 0; i < MAX_IMAGES; i++) {
                if (g_event.img[i][0] == 0) {
                    string_copy(g_event.img[i], ptr); // to end of line
                    g_event.img[i][strlen(ptr)] = 0;
                    return retval;
                }
            }
            break;
        case LABEL_REPORT:
            g_run_mode = RUN_MODE_REPORT;
            break;
        case LABEL_DB_FIX:
            g_run_mode = RUN_MODE_DB_FIX;
            break;
        case LABEL_SHAPE:
            if (toupper(*ptr) == 'F') { // flat curve
                g_event.par_multiple = flat_par_multiple;
                g_event.trophy_multiple = flat_trophy_multiple;
            } else if (toupper(*ptr) == 'S') { // standard curve
                g_event.par_multiple = standard_par_multiple;
                g_event.trophy_multiple = standard_trophy_multiple;
            } else if (toupper(*ptr) == 'H') { // hybrid curve
                g_event.par_multiple = hybrid_par_multiple;
                g_event.trophy_multiple = hybrid_trophy_multiple;
            } else if (toupper(*ptr) == 'D') { // double standard curve
                g_event.par_multiple = double_par_multiple;
                g_event.trophy_multiple = double_trophy_multiple;
            } else if (toupper(*ptr) == 'M') { // muliply curve
                g_event.par_multiple = multiply_par_multiple;
                g_event.trophy_multiple = multiply_trophy_multiple;
            } else if (toupper(*ptr) == 'C') { // custom curve
                g_event.par_multiple = custom_par_multiple;
                g_event.trophy_multiple = flat_trophy_multiple;
                parse_custom_curve_shape(ptr);
                return retval;
            } else {
                fprintf(stderr, "Unknown shape type: %s\n", ptr);
            }
            break;
        case LABEL_GOLD_SHIFT:
            parse_custom_gold_shift(ptr);
            return retval;
            break;
        case LABEL_SQUEEZE:
            g_event.squeeze = atof(ptr);
            g_event.auto_squeeze = FALSE;
            if (g_event.squeeze <= 0.0f) {
                fprintf(stderr, "Failed squeeze parse: '%s' = %.3f\n", ptr, g_event.squeeze);
                g_event.squeeze = DEFAULT_SQUEEZE;
            }
            break;
        case LABEL_SCOOT:
            g_event.auto_scoot = FALSE;
            g_event.scoot = atof(ptr);
            break;
        case LABEL_WEIGHT:
            g_event.weight = atof(ptr);
            if (g_event.weight < 0.0f) {
                fprintf(stderr, "Failed weight parse: '%s' = %.3f\n", ptr, g_event.weight);
                g_event.weight = 1.0f;
            }
            break;
        default:
            if (isgraph(*ptr)) {
                fprintf(stderr, "Failed label parse for '%s'\n", pptr);
            }
            retval--; // didn't find a label after all
            continue; // check "value" token to see if it's a label
        }
        ptr = field_skip(ptr); // skip value
    } while (*ptr && label != LABEL_NONE);

    if (got_entry && player) {
        entry->player_id = player->id;
        if (time_to_usec(&time) > 0) {
            entry->time = time;
        } else if (time_to_usec(&entry->split[0]) > 0) {
            add_splits(entry);
        }
        ov_head = time_insert(ov_head, &time_sort[g_entry_cnt], entry);
        g_entry_cnt++;
    }
    return retval;
}

int
scan_event(FILE *file)
{
    char cur_line[MAX_LINE_LEN];
    if (!file) {
        return 0;
    }
    while (!feof(file) && (g_entry_cnt < MAX_RACERS)) {
        memset(cur_line, 0, MAX_LINE_LEN);
        if (fgets(cur_line, MAX_LINE_LEN-1, file) == 0) {
            fprintf(stderr, "scan_event done: found %d entries; %d players in DB\n", g_entry_cnt, player_cnt);
            return g_entry_cnt;
        }
        event_process_line(cur_line, &entry_db[g_entry_cnt]);
    }
    fprintf(stderr, "scan_event done: max players (%d) exceeded\n", g_entry_cnt);
    return g_entry_cnt;
}

/************************************************/
/* player database                              */
/************************************************/
char *
db_parse_history(char *ptr, race_result_t *race)
{
    label_e label;
    char *pptr;

    if (!ptr || !race) {
        return 0;
    }
    do {
        pptr = ptr;
        label = label_get(ptr);
        ptr = label_skip(ptr);
        switch (label) {
        case LABEL_WEEK:
            race->race_id = atoi(ptr);
            break;
        case LABEL_EVENT_STATUS:
            if (toupper(*ptr) == 'F') {
                race->status = STATUS_FINAL;
            } else if (toupper(*ptr) == 'P') {
                race->status = STATUS_PROVISIONAL;
            } else {
                fprintf(stderr, "History: Unknown status: '%s'\n", ptr);
            }
            break;
        case LABEL_RATING:
            race->rating = atof(ptr);
            break;
        case LABEL_WEIGHT:
            race->weight = atof(ptr);
            if (race->weight < 0.0f) {
                fprintf(stderr, "History: Failed weight parse: '%s' = %.3f\n", ptr, race->weight);
                race->weight = 1.0f;
            }
            break;
        case LABEL_STATUS:
        case LABEL_DISQ:
            if (toupper(*ptr) == 'O') {
                race->dq = DQ_OFF_TRACK;
            } else if (toupper(*ptr) == 'C') {
                race->dq = DQ_CONTACT;
            } else if (toupper(*ptr) == 'R') {
                race->dq = DQ_NO_REPLAY;
            } else if (toupper(*ptr) == 'T') {
                race->dq = DQ_TIME_ERROR;
            } else if (toupper(*ptr) == 'N') {
                race->dq = DQ_NAME_VIOLATION;
            } else if (toupper(*ptr) == 'X') {
                race->dq = DQ_CUSTOM_VIOLATION;
            } else if ((toupper(*ptr) == 'S') || (toupper(*ptr) == 'U')) {
                race->dq = DQ_SUBMITTED;
            } else if (toupper(*ptr) == 'V' || toupper(*ptr) == 'G') {
                race->dq = DQ_VERIFIED;
            } else {
                race->dq = DQ_OK;
            }
            break;
        default:
            return pptr; // points to first unhandled token
        }
        ptr = field_skip(ptr); // skip value
    } while (*ptr && label != LABEL_NONE);

    return ptr;
}

int
db_read_player(char *line)
{
    static player_t *player = 0;
    static int history_idx;
    int retval = 0;
    label_e label;
    char buf[MAX_STR_LEN];
    int len, id;
    char *ptr = line;
    char *pptr;

    if (!line) {
        return 0;
    }
    do {
        pptr = ptr;
        label = label_get(ptr);
        ptr = label_skip(ptr); // skip label
        retval++;
        if (label == LABEL_PLAYER_ID) {
            id = atoi(ptr);
            ptr = field_skip(ptr); // skip field
            if (id <= 0 || id >= MAX_PLAYERS) {
                fprintf(stderr, "bad player id = %d\n", id);
                return 0;
            }
            player = &player_db[id];
            player->id = id;
            player->valid = TRUE;
            player_cnt++;
            history_idx = -1;
            if (id > max_player_id) {
                max_player_id = id;
            }
        } else if (player) {
            switch(label) {
            case LABEL_COMMENT:
                retval--; // skip rest of line
                break;
            case LABEL_NAME:
            case LABEL_PSN:
                field_copy(player->psn, ptr);
                break;
            case LABEL_USER:
                field_copy(player->name, ptr);
                break;
            case LABEL_COUNTRY:
                field_copy(player->country, ptr);
                break;
            case LABEL_DIV:
                player->div = atoi(ptr);
                break;
            case LABEL_SUB_DIV:
                if (isdigit(ptr[0])) {
                    player->sub_div = atoi(ptr);
                } else if (ptr[0] == 'g' || ptr[0] == 'G') {
                    player->sub_div = SUB_DIV_GOLD;
                } else if (ptr[0] == 's' || ptr[0] == 'S') {
                    player->sub_div = SUB_DIV_SILVER;
                } else if (ptr[0] == 'b' || ptr[0] == 'B') {
                    player->sub_div = SUB_DIV_BRONZE;
                }
                break;
            case LABEL_REAL_RATING:
                if (atof(ptr) > 0.0f) {
                    player->real_rating = atof(ptr);
                    if (player->rating <= 0.0f) {
                        player->rating = player->real_rating;
                    }
                }
                break;
            case LABEL_RATING:
                if (atof(ptr) > 0.0f) {
                    player->rating = atof(ptr);
                    // fix for real rating introduction
                    if (player->real_rating <= 0.0f) {
                        player->real_rating = player->rating;
                    }
                }
                break;
            case LABEL_WEIGHT:
                player->total_weight = atof(ptr);
                break;
            case LABEL_EVENT_CNT:
                player->event_count = atoi(ptr);
                break;
            case LABEL_DQ_CNT:
                player->dq_count = atoi(ptr);
                break;
            case LABEL_VERIFIED_CNT:
                player->verified_count = atoi(ptr);
                break;
            case LABEL_QUALIFIER:
                player->qualifier.race_id = 0;
                ptr = db_parse_history(ptr, &player->qualifier);
                continue; // avoid value field_skip
            case LABEL_HISTORY:
                history_idx++;
                if (history_idx < RACE_HISTORY) {
                    ptr = db_parse_history(ptr, &player->history[history_idx]);
                    continue; // avoid value field_skip
                } else {
                    fprintf(stderr, "LABEL_HISTORY: too much history (%d) for player %d\n", history_idx, id);
                }
                break;
            }
            ptr = field_skip(ptr); // skip value
        }
    } while (*ptr && label != LABEL_NONE);

    return 0;
}

int
db_read(FILE *file)
{
    char cur_line[MAX_LINE_LEN];

    if (!file) {
        return 0;
    }

    while (!feof(file) && (player_cnt < MAX_PLAYERS)) {
        memset(cur_line, 0, MAX_LINE_LEN);
        if (fgets(cur_line, MAX_LINE_LEN-1, file) == 0) {
            fprintf(stderr, "db_read done: found %d players\n", player_cnt);
            return player_cnt;
        }
        db_read_player(cur_line);
    }
    return player_cnt;
}

int
db_write_player(FILE *file, player_t *player)
{
    char line[MAX_LINE_LEN];
    int retval = 0, len, i;
    race_result_t *rr;

    if (!file || !player) {
        return 0;
    }

    retval = sprintf(line, "Player_id: %d User: \"%s\" PSN: \"%s\" Div: %d Sub: %c Rating: %f RRating: %f Weight: %f Events: %d DQS: %d VERI: %d ", player->id, player->name, player->psn, player->div, g_subdiv_text[player->sub_div][0], player->rating, player->real_rating, player->total_weight, player->event_count, player->dq_count, player->verified_count);
    if (retval) {
        if (*player->country) {
            retval = fprintf(file, "%s Country: \"%s\"\n", line, player->country);
        } else {
            fprintf(file, "%s\n", line);
        }
    }
    if (player->qualifier.status != STATUS_NONE) {
        rr = &player->qualifier;
        len = sprintf(line, "Qual: Event_Status: %c Rating: %f Weight: %f %s%s", (rr->status == STATUS_FINAL ? 'F' : 'P'), rr->rating, rr->weight, (rr->dq ? "DISQ: " : ""), (rr->dq ? g_dq_text[rr->dq] : ""));
        retval += len;
        if (len) {
            fprintf(file, "%s\n", line);
        }
    }
    for (i = 0, rr = &player->history[i];
            i < RACE_HISTORY && rr->status != STATUS_NONE;
            i++, rr = &player->history[i]) {
        len = sprintf(line, "History: Week: %d Event_Status: %c Rating: %f Weight: %f %s%s", rr->race_id, (rr->status == STATUS_FINAL ? 'F' : 'P'), rr->rating, rr->weight, (rr->dq ? "DISQ: " : ""), (rr->dq ? g_dq_text[rr->dq] : ""));
        retval += len;
        if (len) {
            fprintf(file, "%s\n", line);
        }
    }

    return retval;
}

int
db_write(FILE *file)
{
    player_t *player;
    player_iter_t iter;
    int retval = 0;

    if (!file) {
        return 0;
    }

    fprintf(file, "# WRS DB START\n\n");
    for (player = player_get_first(&iter); player; player = player_get_next(&iter)) {
        if (db_write_player(file, player)) {
            retval++;
        }
    }
    fprintf(file, "\n# WRS DB END\n");
    return retval;
}

void
race_result_set(player_t *player, unsigned week, unsigned status, dq_reason_e dq, double weight, double rating)
{
    race_result_t *rr = &player->latest;

    rr->race_id = week;
    rr->status = status;
    rr->dq = dq;
    rr->weight = weight * weight_adjust(player->rating, rating);
    rr->rating = rating;
}

void
race_result_swap(race_result_t *a, race_result_t *b)
{
    if (a && b) {
        race_result_t tmp;
        tmp = *a;
        *a = *b;
        *b = tmp;
    }
}

void
db_update()
{
    player_t *player;
    entry_t *cur;
    entry_iter_t iter;
    unsigned i;
    unsigned fold_rating = FALSE;
    unsigned update_done;
    unsigned oldest_history;
    race_result_t tmp;

    // XXX: tmp
    for (cur = entry_get_first(&iter, ov_head, DIV_ALL, ITER_DQ_ALL); cur; cur = entry_get_next(&iter)) {
        oldest_history = 999999;
        player = player_get(cur->player_id);
        if (player && player->valid) {
            race_result_set(player, g_event.week, g_event.status, cur->dq, g_event.weight, cur->rating);
            fold_rating = FALSE;
            if (g_event.status == STATUS_FINAL) {
                fold_rating = TRUE; // will fold, unless already accounted for
            }
            if (g_event.week == EVENT_QUALIFIER) { // qualifier check
                if (player->qualifier.status == STATUS_FINAL) {
                    // already accounted for
                    fold_rating = FALSE;
                } else {
                    player->qualifier = player->latest;
                }
            } else { // update history
                update_done = FALSE;
                for (i = 0; i < RACE_HISTORY; i++) {
                    if (oldest_history > player->history[i].race_id) {
                        oldest_history = player->history[i].race_id;
                    }
                    if (player->history[i].race_id == player->latest.race_id) {
                        if (player->history[i].status == STATUS_FINAL) {
                            fold_rating = FALSE;
                        }
                        player->history[i] = player->latest;
                        update_done = TRUE;
                        break;
                    }
                }
                if (update_done == FALSE) {
                    if (oldest_history > player->latest.race_id) {
                        fprintf(stderr, "db_update() race %d too old to update for racer %s\n", player->latest.race_id, player->psn);
                        fold_rating = FALSE;
                    } else {
                        tmp = player->latest;
                        for (i = 0; i < RACE_HISTORY; i++) {
                            race_result_swap(&tmp, &player->history[i]);
                        }
                    }
                }
            }
            if (fold_rating == TRUE) {
                player_update_rating(player);
// obsolete
//                if (g_event.week == EVENT_QUALIFIER) {
//                    player_div_set(player->id, player->rating);
//                }
            }
        }
    }
}

/************************************************/
/* output                                       */
/************************************************/
void
rating_string(char *buffer, entry_t *e)
{
    int i;
    int thumb_cnt = 0;

    *buffer = 0; // null terminate

    if (dq_ok(e->dq)) {
        // only :tup: when 3+ racer in div res
        if (div_stat[entry_div(e)].count >=3 && e->hcp_delta <= -SUB_DIVISION_RANGE) {
    //        thumb_cnt = -(3.0f * e->hcp_delta);
            thumb_cnt = 1;
    //    } else if (e->prov_div < entry_div(e)) {
    //        thumb_cnt = 1;
        }
        for (i = 0; i < thumb_cnt; i++) {
            // XXX: tmp remove this
//            strcat(buffer, ":tup:");
        }
    }
}

void
dump_entry(FILE *file, entry_t *e, display_opt_e opt, int place)
{
    int i;
    char rating[MAX_NAME_LEN];
    player_t *player;

    rating[0] = 0;
    if (g_event.week == EVENT_QUALIFIER) {
        player = player_get(e->player_id);
        if (!player) {
            return;
        }
        if (opt != SHOW_RATINGS) { // for display
            fprintf(file, "%s / %s / %s (",
                player->psn, player->name, player_country(e->player_id));
            if (player->qualifier.rating > 0.0f) {
                // if it's stored, use that
                fprintf(file, "%1.3f", player->qualifier.rating);
            } else {
                // else, use the event rating
                fprintf(file, "%1.3f", e->rating);
            }
            if (player->event_count > 1) {
                fprintf(file, " / %1.3f", player->rating);
            }
            // TODO: qualifier hack
//            fprintf(file, ") %s \n", g_dq_display_text[e->dq]);
            fprintf(file, ") \n");
        } else { // private
            fprintf(file, "%s / %s %s (%1.3f) \n",
                entry_psn(e), player_name(e->player_id),
                time_display(&e->time), e->rating);
        }
        return; // done with entry, so exit
    } else if (!dq_ok(e->dq)) {
        fprintf(file, "%sQ---%s---%s ", g_color_tag[entry_div(e)],
                g_dq_display_text[e->dq], entry_psn(e));
        if (e->dq >= DQ_NO_REPLAY) {
            fprintf(file, "%s ", g_dq_flag_url[FLAG_BLACK]);
        } else {
            fprintf(file, "%s ", g_dq_flag_url[FLAG_RED]);
        }
    } else if (place < 10) {
        if (opt == SHOW_RATING_DELTA) {
            int usec;
            ttime_t time;
            usec = time_handicap(e);
            time_from_usec(&time, usec);
            fprintf(file, "%s%u---%s---(%s)-%c-%s ", g_color_tag[entry_div(e)],
                    place, time_display(&time), rating_delta_display(e),
                    entry_rookie(e), entry_psn(e));
//            fprintf(file, "%s%u--(%s)---%s ", g_color_tag[entry_div(e)],
//                    place, rating_delta_display(e), entry_psn(e));
        } else if (event_season_active() && opt == SHOW_FLAGS) {
            fprintf(file, "%s%u---%s---%u-%c-%s ", g_color_tag[entry_div(e)],
                    place, time_display(&e->time), e->points,
                    entry_rookie(e), entry_psn(e));
        } else {
            fprintf(file, "%s%u---%s-%c-%s ", g_color_tag[entry_div(e)],
                    place, time_display(&e->time), 
                    entry_rookie(e), entry_psn(e));
        }
    } else {
        if (opt == SHOW_RATING_DELTA) {
            int usec;
            ttime_t time;
            usec = time_handicap(e);
            time_from_usec(&time, usec);
            fprintf(file, "%s%u--%s---(%s)-%c-%s ", g_color_tag[entry_div(e)],
                    place, time_display(&time), rating_delta_display(e),
                    entry_rookie(e), entry_psn(e));
//            fprintf(file, "%s%u--(%s)---%s ", g_color_tag[entry_div(e)],
//                    place, rating_delta_display(e), entry_psn(e));
        } else if (event_season_active() && opt == SHOW_FLAGS) {
            fprintf(file, "%s%u--%s---%u-%c-%s ", g_color_tag[entry_div(e)],
                    place, time_display(&e->time), e->points, entry_rookie(e), entry_psn(e));
        } else {
            fprintf(file, "%s%u--%s-%c-%s ", g_color_tag[entry_div(e)],
                    place, time_display(&e->time), entry_rookie(e), entry_psn(e));
        }
    }
    if (opt == SHOW_FLAGS) {
        rating_string(rating, e);
        fprintf(file, "%s %s %s", rating, entry_replay_string(e), entry_dq_flag(e));
    } else if (opt == SHOW_RATINGS) {
        fprintf(file, "r=%.3f ", e->rating);
        fprintf(file, "(d%d/%.3f) ", e->prov_div, e->hcp_delta);
    } else if (opt == SHOW_ALL_TIMES) {
        for (i = 0; i < MAX_SPLITS; i++) {
            if (time_to_usec(&e->split[i])) {
                fprintf(file, "%s ", time_display(&e->split[i]));
            }
        }
    }
    fprintf(file, "[/COLOR]\n");
}

void
dump_qualifier_subdiv_heading(FILE *file, int div, int subdiv)
{
    switch(subdiv) {
    case SUB_DIV_GOLD:
        fprintf(file, "\n[color=Gold][B][size=4]Division %d Gold (%d.000 - %d.333):[/size][/B][/COLOR]\n\n", div, (div==1?0:div), div);
        break;
    case SUB_DIV_SILVER:
        fprintf(file, "\n[color=Silver][B][size=4]Division %d Silver (%d.334 - %d.666):[/size][/B][/COLOR]\n\n", div, div, div);
        break;
    case SUB_DIV_BRONZE:
        fprintf(file, "\n[color=#B88A00][B][size=4]Division %d Bronze (%d.667 - %d.999):[/size][/B][/COLOR]\n\n", div, div, div);
        break;
    }
}

void
dump_qualifier(FILE *file)
{
    entry_t *cur, *prior;
    player_t *player;
    entry_iter_t iter;
    int i, div, subdiv, title_printed, subdiv_printed;

    // heading
    fprintf(file, "[center][IMG]https://www.gtplanet.net/forum/attachments/wrs-tt-main-banner-png.693509/[/IMG]\n");
    fprintf(file, "\n[B][size=6]:: Official GTSport WRS Registry ::[/size][/b][/center]\n\n");
            
#if 0
    for (div = 1; div <= DIV_COUNT; div++) {
        title_printed = FALSE;
        for (subdiv = SUB_DIV_GOLD; subdiv <= SUB_DIV_BRONZE; subdiv++) {
            subdiv_printed = FALSE;
            cur = entry_get_first(&iter, ov_head, div, ITER_DQ_OK);
            if (!cur) {
                continue;
            }
            prior = 0;
            for (i = 1; cur; i++, cur = entry_get_next(&iter)) {
                if (player_subdiv(cur->player_id) != subdiv ||
                        player_is_rookie(cur->player_id)) {
                    continue;
                }
                if (title_printed == FALSE) {
                    title_printed = TRUE;
                    fprintf(file, "\n\n[CENTER][B][size=6]:: Division %d ::[/size][/b][/CENTER]\n\n", div);
                }
                if (subdiv_printed == FALSE) {
                    subdiv_printed = TRUE;
                    dump_qualifier_subdiv_heading(file, div, subdiv);
                }
                dump_entry(file, cur, SHOW_NONE, cur->place);
                prior = cur;
            }
        }
    }
#else
    for (div = 1; div <= DIV_COUNT; div++) {
        title_printed = FALSE;
        for (subdiv = SUB_DIV_GOLD; subdiv <= SUB_DIV_BRONZE; subdiv++) {
            player_link_t *plink = player_sort(div, subdiv);
            subdiv_printed = FALSE;
            for (; plink->player != 0; plink++) {
                player = plink->player;
                if (title_printed == FALSE) {
                    title_printed = TRUE;
                    fprintf(file, "\n\n[CENTER][B][size=6]:: Division %d ::[/size][/b][/CENTER]\n\n", div);
                }
                if (subdiv_printed == FALSE) {
                    subdiv_printed = TRUE;
                    dump_qualifier_subdiv_heading(file, div, subdiv);
                }
                fprintf(file, "%s / %s / %s (%1.3f",
                    player->psn, player->name, player_country(player->id), player->rating);
                if (player->qualifier.rating > 0.0f) {
                    // print qualifier rating if we have one
                    fprintf(file, " / %1.3f", player->qualifier.rating);
                }
                fprintf(file, ") \n");
            }
        }
    }
#endif
    // rookies
    title_printed = FALSE;
    for (i = 1; i < player_cnt; i++) {
        player = &player_db[i];
        if (!player || !player_is_rookie(i) || player->verified_count == 0) {
            continue;
        }
        if (title_printed == FALSE) {
            title_printed = TRUE;
            fprintf(file, "\n\n[CENTER][B][size=6]:: Rookies ::[/size][/b][/CENTER]\n\n", div);
        }
//        fprintf(file, "%s / %s (%1.3f) \n", player->psn, player->name, player->rating);
        fprintf(file, "%s / %s / %s (%1.3f handicap) %d events \n",
                player->psn, player->name, player->country, player->rating, player->verified_count);
    }

    fprintf(stdout, "\nNew Qualifier Results:\n");
    for (div = 1; div <= DIV_COUNT; div++) {
        title_printed = FALSE;
        for (subdiv = SUB_DIV_GOLD; subdiv <= SUB_DIV_BRONZE; subdiv++) {
            subdiv_printed = FALSE;
            cur = entry_get_first(&iter, ov_head, div, ITER_DQ_OK);
            if (!cur) {
                continue;
            }
            prior = 0;
            for (i = 1; cur; i++, cur = entry_get_next(&iter)) {
                if (player_subdiv(cur->player_id) != subdiv) {
                    continue;
                }
                player = player_get(cur->player_id);
                if (player->qualifier.status == STATUS_FINAL) {
                    // already accounted for
                    continue;
                }
                if (title_printed == FALSE) {
                    title_printed = TRUE;
                    fprintf(stdout, "\n[B][size=4]:: Division %d ::[/size][/b]\n\n", div);
                }
                if (subdiv_printed == FALSE) {
                    subdiv_printed = TRUE;
                    dump_qualifier_subdiv_heading(stdout, div, subdiv);
                }
                dump_entry(stdout, cur, SHOW_NONE, cur->place);
                prior = cur;
            }
        }
    }

    fprintf(stdout, "\nOverall Results:\n\n");
    div = 1;
    for (i = 1, cur = entry_get_first(&iter, ov_head, DIV_ALL, ITER_DQ_OK); cur; i++, cur = entry_get_next(&iter)) {
        if (time_to_usec(&cur->time) >= time_to_usec(&div_stat[div].par)) {
            fprintf(stdout, "\n>> Division %d: ", div);
            fprintf(stdout, "Par: %s ", time_display(&div_stat[div].par));
            fprintf(stdout, "Gold: %s ", time_display(&div_stat[div].gold));
            fprintf(stdout, "Silver: %s ", time_display(&div_stat[div].silver));
            fprintf(stdout, "Bronze: %s\n", time_display(&div_stat[div].bronze));
            div++;
        } 
        //dump_entry(stdout, cur, SHOW_ALL_TIMES, cur->overall_place);
        dump_entry(stdout, cur, SHOW_RATINGS, cur->overall_place);
    }
    fprintf(stdout, "\nDisqualifications:\n");

    for (cur = entry_get_first(&iter, ov_head, DIV_ALL, ITER_DQ_BAD); cur; cur = entry_get_next(&iter)) {
        dump_entry(stdout, cur, SHOW_NONE, cur->overall_place);
    }
}

void
dump_event(FILE *file)
{
    entry_t *cur;
    entry_iter_t iter;
    int i, div;

    // heading
    fprintf(file, "\n%sWeek %d (%s): %s", g_results_text_1, g_event.week,
            g_event.status==STATUS_FINAL?"Official":"Provisional",
            g_event.description);
    fprintf(file, "%s%s", g_results_text_2a, g_event.img[0]);
    fprintf(file, "%s%s", g_results_text_2b, g_event.img[1]);
    fprintf(file, "%s%s", g_results_text_2c, g_event.car[0]?g_event.car:"xxx_CAR");
    fprintf(file, "%s%s", g_results_text_3a, g_event.img[2]);
    fprintf(file, "%s%s", g_results_text_3b, g_event.track[0]?g_event.track:"xxx_TRACK");
    fprintf(file, "%s%s%s", g_results_text_4a, g_event.comment, g_results_text_4b);
    fprintf(file, "[LIST][*]gtpwrs%03d, essentials, pineapple[/LIST]\n", g_event.week);
    fprintf(file, "%s", g_results_text_4c);

    for (div = 1; div <= DIV_COUNT; div++) {
        cur = entry_get_first(&iter, ov_head, div, ITER_DQ_OK);
        if (!cur) {
            continue;
        }
        fprintf(file, "\nDivision %d:\n\n", div);
        for (i = 1; cur; i++, cur = entry_get_next(&iter)) {
            dump_entry(file, cur, SHOW_FLAGS, cur->place);
        }
        for (cur = entry_get_first(&iter, ov_head, div, ITER_DQ_BAD); cur; cur = entry_get_next(&iter)) {
            dump_entry(file, cur, SHOW_NONE, cur->place);
        }
    }

    fprintf(file, "\n[img]%s[/img]\n", g_event.img[3]);
    fprintf(file, "\nOverall Results:\n\n");
    div = 1;
    for (i = 1, cur = entry_get_first(&iter, ov_head, DIV_ALL, ITER_DQ_OK); cur; i++, cur = entry_get_next(&iter)) {
        if (time_to_usec(&cur->time) >= time_to_usec(&div_stat[div].par)) {
            fprintf(file, "\n>> Division %d: ", div);
            fprintf(file, "Par: %s ", time_display(&div_stat[div].par));
            fprintf(file, "Gold: %s ", time_display(&div_stat[div].gold));
            fprintf(file, "Silver: %s ", time_display(&div_stat[div].silver));
            fprintf(file, "Bronze: %s\n", time_display(&div_stat[div].bronze));
            div++;
        } 
        //dump_entry(file, cur, SHOW_ALL_TIMES, cur->overall_place);
        dump_entry(file, cur, SHOW_RATINGS, cur->overall_place);
    }
    fprintf(file, "\n");
    for (cur = entry_get_first(&iter, ov_head, DIV_ALL, ITER_DQ_BAD); cur; cur = entry_get_next(&iter)) {
        dump_entry(file, cur, SHOW_NONE, cur->overall_place);
    }

    fprintf(file, "\n[img]%s[/img]\n", g_event.img[4]);
    fprintf(file, "\nHandicapped Results:\n\n");
    for (i = 1, cur = entry_get_first(&iter, rat_head, DIV_ALL, ITER_DQ_OK); cur; cur = entry_get_next(&iter)) {
        if (entry_rookie(cur) == '-') { // not rookie
            dump_entry(file, cur, SHOW_RATING_DELTA, i++);
        }
    }
    fprintf(file, "\n");
    for (cur = entry_get_first(&iter, rat_head, DIV_ALL, ITER_DQ_BAD); cur; cur = entry_get_next(&iter)) {
        dump_entry(file, cur, SHOW_NONE, cur->overall_place);
    }

    fprintf(file, "\n(Settings: Weight = %.3f Squeeze = %.3f Scoot = %.3f)\n\n",
            g_event.weight, g_event.squeeze, g_event.scoot);
    fprintf(file, "%s", g_results_text_5);
}

void
dump_stats(FILE *file, int detail)
{
    int div, i;
    entry_t *e;
    entry_iter_t iter;
    stat_t *stat;
    ttime_t delta;

    // info
    fprintf(file, "\nWRS Stats for Week %d (%s):\n", g_event.week,
            g_event.status==STATUS_FINAL?"Official":"Provisional");
    if (g_event.description[0]) {
        fprintf(file, "%s\n", g_event.description);
    }
    if (g_event.car[0]) {
        fprintf(file, "Car: %s\n", g_event.car);
    }
    if (g_event.track[0]) {
        fprintf(file, "Track: %s\n", g_event.track);
    }
    fprintf(file, "(Settings: Weight = %.3f Squeeze = %.3f Scoot = %.3f)\n",
            g_event.weight, g_event.squeeze, g_event.scoot);

    fprintf(file, "\nStatistics: ");
    fprintf(file, "\n\nOverall Mean time: %s ", time_display(&ostat.mean));
    if (detail) {
        fprintf(file, "Dev/Min: %.3f ",
            (ostat.mean.time > 0.0f) ? ostat.std_dev*60.0f/ostat.mean.time : 0.0f);
    }
    fprintf(file, "Deviation: %.3f \n", ostat.std_dev);
    fprintf(file, "Quality Mean time: %s ", time_display(&ostat.q_mean));
    if (detail) {
        fprintf(file, "Dev/Min: %.3f ",
            (ostat.q_mean.time > 0.0f) ? ostat.q_std_dev*60.0f/ostat.q_mean.time : 0.0f);
    }
    fprintf(file, "Deviation: %.3f \n", ostat.q_std_dev);
    if (detail) {
        fprintf(file, "    average hcp delta: %.3f\n", ostat.hcp_delta);
        if (file != stdout) { // dump this to stdout if we aren't already
            printf("Overall average hcp delta: %.3f\n", ostat.hcp_delta);
        }
    }
    for (div = 1; div <= DIV_IN_USE; div++) {
        stat = &div_stat[div];

        if (stat->mean.time <= 0.0f) {
            continue;
        }
        if (!detail) {
            fprintf(file, "%s >>> Division %d: ", g_color_tag[div], div);
        } else {
            fprintf(file, "D%d: ", div);
        }
        fprintf(file, "Mean: %s ", time_display(&stat->mean));
        fprintf(file, "Dev: %.3f ", stat->std_dev);
        if (detail) {
            fprintf(file, "Dev/Min: %.3f ", 
                (stat->mean.time > 0.0f) ? stat->std_dev*60.0f/stat->mean.time : 0.0f);
            fprintf(file, "Par: %s \n", time_display(&stat->par));
            fprintf(file, "    q_mean = %s ", time_display(&stat->q_mean));
            fprintf(file, "q_dev = %.3f, q_dev/min = %.3f\n", stat->q_std_dev,
                (stat->q_mean.time > 0.0f) ? stat->q_std_dev*60.0f/stat->q_mean.time : 0.0f);
            fprintf(file, "    -(%d %d %d)+ average hcp delta: %.3f",
                stat->perf[0], stat->perf[1], stat->perf[2], stat->hcp_delta);
            if (file != stdout) { // dump this to stdout if we aren't already
                printf("D%d: -(%d %d %d)+ average hcp delta: %.3f\n", div,
                    stat->perf[0], stat->perf[1], stat->perf[2], stat->hcp_delta);
            }
        } else {
            fprintf(file, "[/color]");
        }
        fprintf(file, "\n");
    }
    if (detail && g_event.week != EVENT_QUALIFIER) {
        fprintf(file, "\nWatch List:\n");
        for (div = 1; div <= DIV_COUNT; div++) {
            for (e = entry_get_first(&iter, ov_head, div, ITER_DQ_OK); e; e = entry_get_next(&iter)) {
                for (i = 0; i < (int)-(e->hcp_delta*3.0f); i++) {
                    fprintf(file, "*");
                }
                if (entry_watch(e)) {
                    fprintf(file, " %s D%d %s >>> D%d %s (rating %.3f hcp delta %.3f)\n",
                            entry_psn(e),
                            entry_div(e), g_subdiv_text[entry_subdiv(e)],
                            e->prov_div, g_subdiv_text[(int)((e->rating-e->prov_div)*3)],
                            e->rating, e->hcp_delta);
                }
            }
        }
        fprintf(file, "\nStruggle List:\n");
        for (div = 1; div <= DIV_COUNT; div++) {
            for (e = entry_get_first(&iter, ov_head, div, ITER_DQ_OK); e; e = entry_get_next(&iter)) {
                if (entry_struggle(e)) {
                    fprintf(file, " %s D%d %s >>> D%d %s (rating %.3f hcp delta %.3f)\n",
                            entry_psn(e),
                            entry_div(e), g_subdiv_text[entry_subdiv(e)],
                            e->prov_div, g_subdiv_text[(int)((e->rating-e->prov_div)*3)],
                            e->rating, e->hcp_delta);

                }
            }
        }
    }
    if (detail) {
        fprintf(file, "\nDivision thresholds:\n");
        for (div = 0; div <= DIV_IN_USE; div++) {
            fprintf(file, "D%d Par: (%s) ", div, time_display(&div_stat[div].par));
            fprintf(file, "G: (%s) ", time_display(&div_stat[div].gold));
            fprintf(file, "S: (%s) ", time_display(&div_stat[div].silver));
            fprintf(file, "B: (%s) ", time_display(&div_stat[div].bronze));
            time_subtract(&delta, &div_stat[div].bronze, &div_stat[div].par);
            fprintf(file, "range: (%.3f)\n", delta.time);
        }
    }
}

/************************************************/
void
dump_promotion_report(FILE *file, int detail)
{
    player_t *player;
    player_iter_t iter;
    int p_div, i;
    double delta;
    int update_db = FALSE;
    int double_promotion = FALSE;

    if (g_event.status == STATUS_FINAL) {
        update_db = TRUE;
    }

    fprintf(file, "-------------- promotions -----------------\n");
    for (player = player_get_first(&iter); player; player = player_get_next(&iter)) {
        delta = (player->div*3 + player->sub_div + 1) - (player->rating*3);
        if (player->verified_count < MIN_PROMOTION_EVENT_COUNT) {
            continue;
        }
        if ((player->div > 1 || player->sub_div > 0) &&
                (player->rating != 0.0f) && (delta > 1.0)) {
//            ((int)(player->rating*3) < (player->div*3 + player->sub_div))) {
            p_div = (int)player->rating;
            fprintf(file, "%.3f ", player->rating);
            for (i = 2; i < delta; i++) {
                fprintf(file, "*");
                double_promotion = TRUE;
            }
            fprintf(file, " %s (@%s) D%d %s -> D%d %s (%.5f -%.5f)\n",
                    player->psn, player->name,
                    player->div, g_subdiv_text[player->sub_div],
                    p_div, g_subdiv_text[(int)(3*(player->rating-p_div))],
                    player->rating, delta/3.0f);
            if (update_db == TRUE) {
                player->div = p_div;
                player->sub_div = (int)(3*(player->rating-p_div));
            }
        }
    }
    if (double_promotion == TRUE) {
        fprintf(file, "9.999 * Denotes double promotion\n");
    }
    fprintf(file, "----------- rookie placement --------------\n");
    for (player = player_get_first(&iter); player; player = player_get_next(&iter)) {
        if ((player->div == 0) && (player_is_rookie(player->id)==FALSE)) {
            p_div = (int)player->rating;
            fprintf(file, "9%.3f %s (@%s) -> D%d %s (%.5f)\n",
                    player->rating, player->psn, player->name,
                    p_div, g_subdiv_text[(int)(3*(player->rating-p_div))],
                    player->rating, delta/3.0f);
            if (update_db == TRUE) {
                player->div = p_div;
                player->sub_div = (int)(3*(player->rating-p_div));
            }
        }
    }
    fprintf(file, "---------------------------------\n");
}

/************************************************/
// this is used to fix screwups in the database
void
player_fix_total_weight(player_t *p)
{
    race_result_t *rr;
    int i;
    double wt=0, rating=0;

    if (p && p->valid) {
        p->qualifier.weight = 2.0f;
        wt = p->qualifier.weight;
        rating = p->qualifier.rating * p->qualifier.weight;
        for (i = RACE_HISTORY-1; i >=0; i--) {
            rr = &p->history[i];
            if (rr->status == STATUS_FINAL && dq_ok(rr->dq)) {
                if (rr->race_id == 1 || rr->race_id == 10) { // wk1=patch; wk10=rally
                    rr->weight = 0.5f;
                } else {
                    rr->weight = 1.0f;
                }
                rr->weight = rr->weight * weight_adjust(rating/wt, rr->rating);
                wt += rr->weight;
                rating += rr->rating * rr->weight;
            }
        }
        if (wt > 0) {
            p->rating = rating / wt;
            p->total_weight = wt;
        }
    }
}

void
fix_all_weight()
{
    player_t *p;
    player_iter_t iter;

    for (p = player_get_first(&iter); p; p = player_get_next(&iter)) {
        player_fix_total_weight(p);
        fprintf(stdout, "update player %s, wt = %.3f\n", p->psn, p->total_weight);
    }
}

/************************************************/
/* main/etc */

void
usage()
{
    fprintf(stderr, "wrsort usage:\n");
    fprintf(stderr, "wrsort <eventfile> [dbfile]\n");
}

int
main(int argc, char **argv)
{
    char eventfilename[MAX_STR_LEN];
    char dbfilename[MAX_STR_LEN];
    FILE *eventfile, *dbfile, *outfile;

    init_db();
    if (argc < 2) {
        usage();
        return -1;
    }
    strcpy(eventfilename, argv[1]);
    if (argc == 3) {
        strcpy(dbfilename, argv[2]);
    } else {
        strcpy(dbfilename, DEFAULT_DB_NAME);
    }
    fprintf(stderr, "------wrsort------\n");
    fprintf(stderr, "input file: %s\n", eventfilename);

    eventfile = fopen(eventfilename, "r");
    if (!eventfile) {
        fprintf(stderr, "wrsort error: file '%s' not found\n", eventfilename);
        return -1;
    }
    dbfile = fopen(dbfilename, "r"); // open for reading

    if (dbfile) {
        fprintf(stderr, "------db read------\n");
        fprintf(stderr, "db file: %s\n", dbfilename);
        db_read(dbfile);
        fclose(dbfile);
    }
    fprintf(stderr, "------parse------\n");
    scan_event(eventfile);
    fclose(eventfile);

    outfile = stdout;
    if (g_event.outfile[0]) {
        outfile = fopen(g_event.outfile, "w"); // overwrite outfile
        if (!outfile) {
            fprintf(stderr, "Failed to open outfile '%s', dumping to stdout\n", g_event.outfile);
            outfile = stdout;
        }
    }
    if (g_run_mode == RUN_MODE_REPORT) {
        dump_promotion_report(outfile, FALSE);
        if (g_event.status != STATUS_FINAL) {
            fprintf(stderr, "-------done-------\n");
            return 0;
        }
    } else if (g_run_mode == RUN_MODE_DB_FIX) {
        fix_all_weight(); 
    } else { 
        fprintf(stderr, "------stats------\n");
        collate_stats();

        fprintf(stderr, "-------results--------\n");
        dump_stats(stdout, FALSE);
        fprintf(stdout, "\n-----------------------------------\n");
        if (g_event.week == EVENT_QUALIFIER) {
            dump_qualifier(outfile);
        } else {
            dump_event(outfile);
        }

        if (strcmp(g_event.outfile, g_event.statfile)) {
            if (outfile != stdout) {
                fclose(outfile);
            }
            outfile = fopen(g_event.statfile, "w"); // overwrite statfile
            if (!outfile) {
                fprintf(stderr, "Failed to open statfile '%s', dumping to stdout\n", g_event.statfile);
                outfile = stdout;
            }
        }

        fprintf(stderr, "-------stats-------\n");
        dump_stats(outfile, TRUE);
    }
    if (outfile != stdout) {
        fclose(outfile);
    }

    dbfile = fopen(dbfilename, "w"); // overwrite database
    if (dbfile) {
        fprintf(stderr, "------db update------\n");
        fprintf(stderr, "db file: %s\n", dbfilename);
        db_update(); // update database
        db_write(dbfile);
        fclose(dbfile);
    } else {
        fprintf(stderr, "Failed to open dbfile '%s'\n", dbfilename);
    }

    fprintf(stderr, "-------done-------\n");
    return 0;
}

