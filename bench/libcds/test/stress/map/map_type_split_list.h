// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef CDSUNIT_MAP_TYPE_SPLIT_LIST_H
#define CDSUNIT_MAP_TYPE_SPLIT_LIST_H

#include "map_type.h"

#include <cds/container/michael_kvlist_hp.h>
#include <cds/container/michael_kvlist_dhp.h>
#include <cds/container/michael_kvlist_rcu.h>
#include <cds/container/michael_kvlist_nogc.h>

#include <cds/container/lazy_kvlist_hp.h>
#include <cds/container/lazy_kvlist_dhp.h>
#include <cds/container/lazy_kvlist_rcu.h>
#include <cds/container/lazy_kvlist_nogc.h>

#include <cds/container/iterable_kvlist_hp.h>
#include <cds/container/iterable_kvlist_dhp.h>

#include <cds/container/split_list_map.h>
#include <cds/container/split_list_map_rcu.h>
#include <cds/container/split_list_map_nogc.h>

#include <cds_test/stat_splitlist_out.h>
#include <cds_test/stat_michael_list_out.h>
#include <cds_test/stat_lazy_list_out.h>
#include <cds_test/stat_iterable_list_out.h>

namespace map {

    template <class GC, typename Key, typename T, typename Traits = cc::split_list::traits >
    class SplitListMap : public cc::SplitListMap< GC, Key, T, Traits >
    {
        typedef cc::SplitListMap< GC, Key, T, Traits > base_class;
    public:
        template <typename Config>
        SplitListMap( Config const& cfg)
            : base_class( cfg.s_nMapSize, cfg.s_nLoadFactor )
        {}

        template <typename Iterator>
        typename std::enable_if< std::is_same< Iterator, typename base_class::iterator>::value, Iterator>::type
        get_begin()
        {
            return base_class::begin();
        }

        template <typename Iterator>
        typename std::enable_if< std::is_same< Iterator, typename base_class::iterator>::value, Iterator>::type
        get_end()
        {
            return base_class::end();
        }

        // for testing
        static constexpr bool const c_bExtractSupported = true;
        static constexpr bool const c_bLoadFactorDepended = true;
        static constexpr bool const c_bEraseExactKey = false;
    };

    template <typename Key, typename T, typename Traits >
    class SplitListMap< cds::gc::nogc, Key, T, Traits> : public cc::SplitListMap< cds::gc::nogc, Key, T, Traits >
    {
        typedef cc::SplitListMap< cds::gc::nogc, Key, T, Traits > base_class;
    public:
        template <typename Config>
        SplitListMap( Config const& cfg)
            : base_class( cfg.s_nMapSize, cfg.s_nLoadFactor )
        {}

        template <typename K>
        bool insert( K const& key )
        {
            return base_class::insert( key ) != base_class::end();
        }

        template <typename K, typename V>
        bool insert( K const& key, V const& val )
        {
            return base_class::insert( key, val ) != base_class::end();
        }

        template <typename K, typename Func>
        bool insert_with( K const& key, Func func )
        {
            return base_class::insert_with( key, func ) != base_class::end();
        }

        template <typename K>
        bool find( K const& key )
        {
            return base_class::find( key ) != base_class::end();
        }

        void clear()
        {}

        // for testing
        static constexpr bool const c_bExtractSupported = true;
        static constexpr bool const c_bLoadFactorDepended = true;
    };

    struct tag_SplitListMap;

    template <typename Key, typename Value>
    struct map_type< tag_SplitListMap, Key, Value >: public map_type_base< Key, Value >
    {
        typedef map_type_base< Key, Value >      base_class;
        typedef typename base_class::key_compare compare;
        typedef typename base_class::key_less    less;
        typedef typename base_class::equal_to    equal_to;
        typedef typename base_class::key_hash    hash;


        // ***************************************************************************
        // SplitListMap based on MichaelList
        struct traits_SplitList_Michael_dyn_cmp: public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::michael_list_tag>
                ,co::hash< hash >
                ,co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,cc::split_list::ordered_list_traits<
                    typename cc::michael_list::make_traits<
                        co::compare< compare >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Michael_dyn_cmp > SplitList_Michael_HP_dyn_cmp;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Michael_dyn_cmp > SplitList_Michael_DHP_dyn_cmp;
        typedef SplitListMap< cds::gc::nogc, Key, Value, traits_SplitList_Michael_dyn_cmp > SplitList_Michael_NOGC_dyn_cmp;
        typedef SplitListMap< rcu_gpi, Key, Value, traits_SplitList_Michael_dyn_cmp > SplitList_Michael_RCU_GPI_dyn_cmp;
        typedef SplitListMap< rcu_gpb, Key, Value, traits_SplitList_Michael_dyn_cmp > SplitList_Michael_RCU_GPB_dyn_cmp;
        typedef SplitListMap< rcu_gpt, Key, Value, traits_SplitList_Michael_dyn_cmp > SplitList_Michael_RCU_GPT_dyn_cmp;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, traits_SplitList_Michael_dyn_cmp > SplitList_Michael_RCU_SHB_dyn_cmp;
#endif

        struct traits_SplitList_Michael_dyn_cmp_swar: public traits_SplitList_Michael_dyn_cmp
        {
            typedef cds::algo::bit_reversal::swar bit_reversal;
        };
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Michael_dyn_cmp_swar > SplitList_Michael_HP_dyn_cmp_swar;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Michael_dyn_cmp_swar > SplitList_Michael_DHP_dyn_cmp_swar;
        typedef SplitListMap< cds::gc::nogc, Key, Value, traits_SplitList_Michael_dyn_cmp_swar > SplitList_Michael_NOGC_dyn_cmp_swar;
        typedef SplitListMap< rcu_gpi, Key, Value, traits_SplitList_Michael_dyn_cmp_swar > SplitList_Michael_RCU_GPI_dyn_cmp_swar;
        typedef SplitListMap< rcu_gpb, Key, Value, traits_SplitList_Michael_dyn_cmp_swar > SplitList_Michael_RCU_GPB_dyn_cmp_swar;
        typedef SplitListMap< rcu_gpt, Key, Value, traits_SplitList_Michael_dyn_cmp_swar > SplitList_Michael_RCU_GPT_dyn_cmp_swar;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, traits_SplitList_Michael_dyn_cmp_swar > SplitList_Michael_RCU_SHB_dyn_cmp_swar;
#endif

        struct traits_SplitList_Michael_dyn_cmp_stat : public traits_SplitList_Michael_dyn_cmp
        {
            typedef cc::split_list::stat<> stat;
            typedef typename cc::michael_list::make_traits<
                co::compare< compare >
                ,co::stat< cc::michael_list::stat<> >
            >::type ordered_list_traits;
        };
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Michael_dyn_cmp_stat > SplitList_Michael_HP_dyn_cmp_stat;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Michael_dyn_cmp_stat > SplitList_Michael_DHP_dyn_cmp_stat;
        typedef SplitListMap< cds::gc::nogc, Key, Value, traits_SplitList_Michael_dyn_cmp_stat> SplitList_Michael_NOGC_dyn_cmp_stat;
        typedef SplitListMap< rcu_gpi, Key, Value, traits_SplitList_Michael_dyn_cmp_stat > SplitList_Michael_RCU_GPI_dyn_cmp_stat;
        typedef SplitListMap< rcu_gpb, Key, Value, traits_SplitList_Michael_dyn_cmp_stat > SplitList_Michael_RCU_GPB_dyn_cmp_stat;
        typedef SplitListMap< rcu_gpt, Key, Value, traits_SplitList_Michael_dyn_cmp_stat > SplitList_Michael_RCU_GPT_dyn_cmp_stat;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, traits_SplitList_Michael_dyn_cmp_stat > SplitList_Michael_RCU_SHB_dyn_cmp_stat;
#endif

        struct traits_SplitList_Michael_dyn_cmp_seqcst: public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::michael_list_tag>
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,co::memory_model< co::v::sequential_consistent >
                ,cc::split_list::ordered_list_traits<
                    typename cc::michael_list::make_traits<
                        co::compare< compare >
                        ,co::memory_model< co::v::sequential_consistent >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Michael_dyn_cmp_seqcst > SplitList_Michael_HP_dyn_cmp_seqcst;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Michael_dyn_cmp_seqcst > SplitList_Michael_DHP_dyn_cmp_seqcst;
        typedef SplitListMap< cds::gc::nogc, Key, Value, traits_SplitList_Michael_dyn_cmp_seqcst> SplitList_Michael_NOGC_dyn_cmp_seqcst;
        typedef SplitListMap< rcu_gpi, Key, Value, traits_SplitList_Michael_dyn_cmp_seqcst > SplitList_Michael_RCU_GPI_dyn_cmp_seqcst;
        typedef SplitListMap< rcu_gpb, Key, Value, traits_SplitList_Michael_dyn_cmp_seqcst > SplitList_Michael_RCU_GPB_dyn_cmp_seqcst;
        typedef SplitListMap< rcu_gpt, Key, Value, traits_SplitList_Michael_dyn_cmp_seqcst > SplitList_Michael_RCU_GPT_dyn_cmp_seqcst;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, traits_SplitList_Michael_dyn_cmp_seqcst > SplitList_Michael_RCU_SHB_dyn_cmp_seqcst;
#endif

        struct traits_SplitList_Michael_st_cmp: public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::michael_list_tag>
                ,cc::split_list::dynamic_bucket_table< false >
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,cc::split_list::ordered_list_traits<
                    typename cc::michael_list::make_traits<
                        co::compare< compare >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Michael_st_cmp > SplitList_Michael_HP_st_cmp;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Michael_st_cmp > SplitList_Michael_DHP_st_cmp;
        typedef SplitListMap< cds::gc::nogc, Key, Value, traits_SplitList_Michael_st_cmp> SplitList_Michael_NOGC_st_cmp;
        typedef SplitListMap< rcu_gpi, Key, Value, traits_SplitList_Michael_st_cmp > SplitList_Michael_RCU_GPI_st_cmp;
        typedef SplitListMap< rcu_gpb, Key, Value, traits_SplitList_Michael_st_cmp > SplitList_Michael_RCU_GPB_st_cmp;
        typedef SplitListMap< rcu_gpt, Key, Value, traits_SplitList_Michael_st_cmp > SplitList_Michael_RCU_GPT_st_cmp;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, traits_SplitList_Michael_st_cmp > SplitList_Michael_RCU_SHB_st_cmp;
#endif

        //HP + less
        struct traits_SplitList_Michael_dyn_less: public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::michael_list_tag>
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,cc::split_list::ordered_list_traits<
                    typename cc::michael_list::make_traits<
                        co::less< less >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Michael_dyn_less > SplitList_Michael_HP_dyn_less;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Michael_dyn_less > SplitList_Michael_DHP_dyn_less;
        typedef SplitListMap< cds::gc::nogc, Key, Value, traits_SplitList_Michael_dyn_less> SplitList_Michael_NOGC_dyn_less;
        typedef SplitListMap< rcu_gpi, Key, Value, traits_SplitList_Michael_dyn_less > SplitList_Michael_RCU_GPI_dyn_less;
        typedef SplitListMap< rcu_gpb, Key, Value, traits_SplitList_Michael_dyn_less > SplitList_Michael_RCU_GPB_dyn_less;
        typedef SplitListMap< rcu_gpt, Key, Value, traits_SplitList_Michael_dyn_less > SplitList_Michael_RCU_GPT_dyn_less;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, traits_SplitList_Michael_dyn_less > SplitList_Michael_RCU_SHB_dyn_less;
#endif


        struct traits_SplitList_Michael_st_less: public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::michael_list_tag>
                ,cc::split_list::dynamic_bucket_table< false >
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,cc::split_list::ordered_list_traits<
                    typename cc::michael_list::make_traits<
                        co::less< less >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Michael_st_less > SplitList_Michael_HP_st_less;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Michael_st_less > SplitList_Michael_DHP_st_less;
        typedef SplitListMap< cds::gc::nogc, Key, Value, traits_SplitList_Michael_st_less> SplitList_Michael_NOGC_st_less;
        typedef SplitListMap< rcu_gpi, Key, Value, traits_SplitList_Michael_st_less > SplitList_Michael_RCU_GPI_st_less;
        typedef SplitListMap< rcu_gpb, Key, Value, traits_SplitList_Michael_st_less > SplitList_Michael_RCU_GPB_st_less;
        typedef SplitListMap< rcu_gpt, Key, Value, traits_SplitList_Michael_st_less > SplitList_Michael_RCU_GPT_st_less;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, traits_SplitList_Michael_st_less > SplitList_Michael_RCU_SHB_st_less;
#endif

        struct traits_SplitList_Michael_st_less_stat : traits_SplitList_Michael_st_less
        {
            typedef cc::split_list::stat<> stat;
            typedef typename cc::michael_list::make_traits<
                co::less< less >
                , co::stat< cc::michael_list::stat<> >
            >::type ordered_list_traits;

        };
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Michael_st_less_stat > SplitList_Michael_HP_st_less_stat;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Michael_st_less_stat > SplitList_Michael_DHP_st_less_stat;
        typedef SplitListMap< cds::gc::nogc, Key, Value, traits_SplitList_Michael_st_less_stat> SplitList_Michael_NOGC_st_less_stat;
        typedef SplitListMap< rcu_gpi, Key, Value, traits_SplitList_Michael_st_less_stat > SplitList_Michael_RCU_GPI_st_less_stat;
        typedef SplitListMap< rcu_gpb, Key, Value, traits_SplitList_Michael_st_less_stat > SplitList_Michael_RCU_GPB_st_less_stat;
        typedef SplitListMap< rcu_gpt, Key, Value, traits_SplitList_Michael_st_less_stat > SplitList_Michael_RCU_GPT_st_less_stat;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, traits_SplitList_Michael_st_less_stat > SplitList_Michael_RCU_SHB_st_less_stat;
#endif


        // ***************************************************************************
        // SplitListMap based on LazyKVList

        struct SplitList_Lazy_dyn_cmp :
            public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::lazy_list_tag>
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,cc::split_list::ordered_list_traits<
                    typename cc::lazy_list::make_traits<
                        co::compare< compare >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, SplitList_Lazy_dyn_cmp > SplitList_Lazy_HP_dyn_cmp;
        typedef SplitListMap< cds::gc::DHP, Key, Value, SplitList_Lazy_dyn_cmp > SplitList_Lazy_DHP_dyn_cmp;
        typedef SplitListMap< cds::gc::nogc, Key, Value, SplitList_Lazy_dyn_cmp> SplitList_Lazy_NOGC_dyn_cmp;
        typedef SplitListMap< rcu_gpi, Key, Value, SplitList_Lazy_dyn_cmp > SplitList_Lazy_RCU_GPI_dyn_cmp;
        typedef SplitListMap< rcu_gpb, Key, Value, SplitList_Lazy_dyn_cmp > SplitList_Lazy_RCU_GPB_dyn_cmp;
        typedef SplitListMap< rcu_gpt, Key, Value, SplitList_Lazy_dyn_cmp > SplitList_Lazy_RCU_GPT_dyn_cmp;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, SplitList_Lazy_dyn_cmp > SplitList_Lazy_RCU_SHB_dyn_cmp;
#endif

        struct SplitList_Lazy_dyn_cmp_stat : public SplitList_Lazy_dyn_cmp
        {
            typedef cc::split_list::stat<> stat;
            typedef typename cc::lazy_list::make_traits<
                co::compare< compare >
                , co::stat< cc::lazy_list::stat<>>
            >::type ordered_list_traits;
        };
        typedef SplitListMap< cds::gc::HP, Key, Value, SplitList_Lazy_dyn_cmp_stat > SplitList_Lazy_HP_dyn_cmp_stat;
        typedef SplitListMap< cds::gc::DHP, Key, Value, SplitList_Lazy_dyn_cmp_stat > SplitList_Lazy_DHP_dyn_cmp_stat;
        typedef SplitListMap< cds::gc::nogc, Key, Value, SplitList_Lazy_dyn_cmp_stat> SplitList_Lazy_NOGC_dyn_cmp_stat;
        typedef SplitListMap< rcu_gpi, Key, Value, SplitList_Lazy_dyn_cmp_stat > SplitList_Lazy_RCU_GPI_dyn_cmp_stat;
        typedef SplitListMap< rcu_gpb, Key, Value, SplitList_Lazy_dyn_cmp_stat > SplitList_Lazy_RCU_GPB_dyn_cmp_stat;
        typedef SplitListMap< rcu_gpt, Key, Value, SplitList_Lazy_dyn_cmp_stat > SplitList_Lazy_RCU_GPT_dyn_cmp_stat;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, SplitList_Lazy_dyn_cmp_stat > SplitList_Lazy_RCU_SHB_dyn_cmp_stat;
#endif

        struct SplitList_Lazy_dyn_cmp_seqcst :
            public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::lazy_list_tag>
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,co::memory_model< co::v::sequential_consistent >
                ,cc::split_list::ordered_list_traits<
                    typename cc::lazy_list::make_traits<
                        co::compare< compare >
                        ,co::memory_model< co::v::sequential_consistent >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, SplitList_Lazy_dyn_cmp_seqcst > SplitList_Lazy_HP_dyn_cmp_seqcst;
        typedef SplitListMap< cds::gc::DHP, Key, Value, SplitList_Lazy_dyn_cmp_seqcst > SplitList_Lazy_DHP_dyn_cmp_seqcst;
        typedef SplitListMap< cds::gc::nogc, Key, Value, SplitList_Lazy_dyn_cmp_seqcst> SplitList_Lazy_NOGC_dyn_cmp_seqcst;
        typedef SplitListMap< rcu_gpi, Key, Value, SplitList_Lazy_dyn_cmp_seqcst > SplitList_Lazy_RCU_GPI_dyn_cmp_seqcst;
        typedef SplitListMap< rcu_gpb, Key, Value, SplitList_Lazy_dyn_cmp_seqcst > SplitList_Lazy_RCU_GPB_dyn_cmp_seqcst;
        typedef SplitListMap< rcu_gpt, Key, Value, SplitList_Lazy_dyn_cmp_seqcst > SplitList_Lazy_RCU_GPT_dyn_cmp_seqcst;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, SplitList_Lazy_dyn_cmp_seqcst > SplitList_Lazy_RCU_SHB_dyn_cmp_seqcst;
#endif

        struct SplitList_Lazy_st_cmp :
            public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::lazy_list_tag>
                ,cc::split_list::dynamic_bucket_table< false >
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,cc::split_list::ordered_list_traits<
                    typename cc::lazy_list::make_traits<
                        co::compare< compare >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, SplitList_Lazy_st_cmp > SplitList_Lazy_HP_st_cmp;
        typedef SplitListMap< cds::gc::DHP, Key, Value, SplitList_Lazy_st_cmp > SplitList_Lazy_DHP_st_cmp;
        typedef SplitListMap< cds::gc::nogc, Key, Value, SplitList_Lazy_st_cmp> SplitList_Lazy_NOGC_st_cmp;
        typedef SplitListMap< rcu_gpi, Key, Value, SplitList_Lazy_st_cmp > SplitList_Lazy_RCU_GPI_st_cmp;
        typedef SplitListMap< rcu_gpb, Key, Value, SplitList_Lazy_st_cmp > SplitList_Lazy_RCU_GPB_st_cmp;
        typedef SplitListMap< rcu_gpt, Key, Value, SplitList_Lazy_st_cmp > SplitList_Lazy_RCU_GPT_st_cmp;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, SplitList_Lazy_st_cmp > SplitList_Lazy_RCU_SHB_st_cmp;
#endif


        struct SplitList_Lazy_dyn_less :
            public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::lazy_list_tag>
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,cc::split_list::ordered_list_traits<
                    typename cc::lazy_list::make_traits<
                        co::less< less >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, SplitList_Lazy_dyn_less > SplitList_Lazy_HP_dyn_less;
        typedef SplitListMap< cds::gc::DHP, Key, Value, SplitList_Lazy_dyn_less > SplitList_Lazy_DHP_dyn_less;
        typedef SplitListMap< cds::gc::nogc, Key, Value, SplitList_Lazy_dyn_less> SplitList_Lazy_NOGC_dyn_less;
        typedef SplitListMap< rcu_gpi, Key, Value, SplitList_Lazy_dyn_less > SplitList_Lazy_RCU_GPI_dyn_less;
        typedef SplitListMap< rcu_gpb, Key, Value, SplitList_Lazy_dyn_less > SplitList_Lazy_RCU_GPB_dyn_less;
        typedef SplitListMap< rcu_gpt, Key, Value, SplitList_Lazy_dyn_less > SplitList_Lazy_RCU_GPT_dyn_less;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, SplitList_Lazy_dyn_less > SplitList_Lazy_RCU_SHB_dyn_less;
#endif

        struct SplitList_Lazy_st_less :
            public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::lazy_list_tag>
                ,cc::split_list::dynamic_bucket_table< false >
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,cc::split_list::ordered_list_traits<
                    typename cc::lazy_list::make_traits<
                        co::less< less >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, SplitList_Lazy_st_less > SplitList_Lazy_HP_st_less;
        typedef SplitListMap< cds::gc::DHP, Key, Value, SplitList_Lazy_st_less > SplitList_Lazy_DHP_st_less;
        typedef SplitListMap< cds::gc::nogc, Key, Value, SplitList_Lazy_st_less> SplitList_Lazy_NOGC_st_less;
        typedef SplitListMap< rcu_gpi, Key, Value, SplitList_Lazy_st_less > SplitList_Lazy_RCU_GPI_st_less;
        typedef SplitListMap< rcu_gpb, Key, Value, SplitList_Lazy_st_less > SplitList_Lazy_RCU_GPB_st_less;
        typedef SplitListMap< rcu_gpt, Key, Value, SplitList_Lazy_st_less > SplitList_Lazy_RCU_GPT_st_less;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, SplitList_Lazy_st_less > SplitList_Lazy_RCU_SHB_st_less;
#endif

        struct SplitList_Lazy_st_less_stat : public SplitList_Lazy_st_less
        {
            typedef cc::split_list::stat<> stat;
            typedef typename cc::lazy_list::make_traits<
                co::less< less >
                , co::stat< cc::lazy_list::stat<>>
            >::type ordered_list_traits;
        };
        typedef SplitListMap< cds::gc::HP, Key, Value, SplitList_Lazy_st_less_stat > SplitList_Lazy_HP_st_less_stat;
        typedef SplitListMap< cds::gc::DHP, Key, Value, SplitList_Lazy_st_less_stat > SplitList_Lazy_DHP_st_less_stat;
        typedef SplitListMap< cds::gc::nogc, Key, Value, SplitList_Lazy_st_less_stat> SplitList_Lazy_NOGC_st_less_stat;
        typedef SplitListMap< rcu_gpi, Key, Value, SplitList_Lazy_st_less_stat > SplitList_Lazy_RCU_GPI_st_less_stat;
        typedef SplitListMap< rcu_gpb, Key, Value, SplitList_Lazy_st_less_stat > SplitList_Lazy_RCU_GPB_st_less_stat;
        typedef SplitListMap< rcu_gpt, Key, Value, SplitList_Lazy_st_less_stat > SplitList_Lazy_RCU_GPT_st_less_stat;
#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED
        typedef SplitListMap< rcu_shb, Key, Value, SplitList_Lazy_st_less_stat > SplitList_Lazy_RCU_SHB_st_less_stat;
#endif


        // ***************************************************************************
        // SplitListMap based on IterableList
        struct traits_SplitList_Iterable_dyn_cmp: public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::iterable_list_tag>
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,cc::split_list::ordered_list_traits<
                    typename cc::iterable_list::make_traits<
                        co::compare< compare >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Iterable_dyn_cmp > SplitList_Iterable_HP_dyn_cmp;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Iterable_dyn_cmp > SplitList_Iterable_DHP_dyn_cmp;

        struct traits_SplitList_Iterable_dyn_cmp_stat : public traits_SplitList_Iterable_dyn_cmp
        {
            typedef cc::split_list::stat<> stat;
            typedef typename cc::iterable_list::make_traits<
                co::compare< compare >
                , co::stat< cc::iterable_list::stat<>>
            >::type ordered_list_traits;
        };
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Iterable_dyn_cmp_stat > SplitList_Iterable_HP_dyn_cmp_stat;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Iterable_dyn_cmp_stat > SplitList_Iterable_DHP_dyn_cmp_stat;

        struct traits_SplitList_Iterable_dyn_cmp_seqcst: public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::iterable_list_tag>
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,co::memory_model< co::v::sequential_consistent >
                ,cc::split_list::ordered_list_traits<
                    typename cc::iterable_list::make_traits<
                        co::compare< compare >
                        ,co::memory_model< co::v::sequential_consistent >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Iterable_dyn_cmp_seqcst > SplitList_Iterable_HP_dyn_cmp_seqcst;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Iterable_dyn_cmp_seqcst > SplitList_Iterable_DHP_dyn_cmp_seqcst;

        struct traits_SplitList_Iterable_st_cmp: public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::iterable_list_tag>
                ,cc::split_list::dynamic_bucket_table< false >
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,cc::split_list::ordered_list_traits<
                    typename cc::iterable_list::make_traits<
                        co::compare< compare >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Iterable_st_cmp > SplitList_Iterable_HP_st_cmp;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Iterable_st_cmp > SplitList_Iterable_DHP_st_cmp;

        //HP + less
        struct traits_SplitList_Iterable_dyn_less: public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::iterable_list_tag>
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,cc::split_list::ordered_list_traits<
                    typename cc::iterable_list::make_traits<
                        co::less< less >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Iterable_dyn_less > SplitList_Iterable_HP_dyn_less;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Iterable_dyn_less > SplitList_Iterable_DHP_dyn_less;

        struct traits_SplitList_Iterable_st_less: public cc::split_list::make_traits<
                cc::split_list::ordered_list<cc::iterable_list_tag>
                ,cc::split_list::dynamic_bucket_table< false >
                ,co::hash< hash >
                , co::item_counter< cds::atomicity::cache_friendly_item_counter >
                ,cc::split_list::ordered_list_traits<
                    typename cc::iterable_list::make_traits<
                        co::less< less >
                    >::type
                >
            >::type
        {};
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Iterable_st_less > SplitList_Iterable_HP_st_less;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Iterable_st_less > SplitList_Iterable_DHP_st_less;

        struct traits_SplitList_Iterable_st_less_stat : traits_SplitList_Iterable_st_less
        {
            typedef cc::split_list::stat<> stat;
            typedef typename cc::iterable_list::make_traits<
                co::less< less >
                , co::stat< cc::iterable_list::stat<>>
            >::type ordered_list_traits;
        };
        typedef SplitListMap< cds::gc::HP, Key, Value, traits_SplitList_Iterable_st_less_stat > SplitList_Iterable_HP_st_less_stat;
        typedef SplitListMap< cds::gc::DHP, Key, Value, traits_SplitList_Iterable_st_less_stat > SplitList_Iterable_DHP_st_less_stat;
    };

    template <typename GC, typename K, typename T, typename Traits >
    static inline void print_stat( cds_test::property_stream& o, SplitListMap< GC, K, T, Traits > const& m )
    {
        o << m.statistics()
          << cds_test::stat_prefix( "list_stat" )
          << m.list_statistics()
          << cds_test::stat_prefix( "" );
    }

}   // namespace map

#define CDSSTRESS_SplitListMap_case( fixture, test_case, splitlist_map_type, key_type, value_type ) \
    TEST_P( fixture, splitlist_map_type ) \
    { \
        typedef map::map_type< tag_SplitListMap, key_type, value_type >::splitlist_map_type map_type; \
        test_case<map_type>(); \
    }

#ifdef CDS_URCU_SIGNAL_HANDLING_ENABLED

#if defined(CDS_STRESS_TEST_LEVEL) && CDS_STRESS_TEST_LEVEL > 1
#   define CDSSTRESS_SplitListMap_SHRCU_2( fixture, test_case, key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHB_dyn_cmp_seqcst,  key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHT_dyn_cmp_seqcst,  key_type, value_type ) \

#else
#   define CDSSTRESS_SplitListMap_SHRCU_2( fixture, test_case, key_type, value_type )
#endif

#if defined(CDS_STRESS_TEST_LEVEL) && CDS_STRESS_TEST_LEVEL == 1
#   define CDSSTRESS_SplitListMap_SHRCU_1( fixture, test_case, key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHT_dyn_cmp,         key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHB_dyn_cmp_stat,    key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHB_st_cmp,          key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHT_st_cmp,          key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHB_dyn_less,        key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHT_st_less,         key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHB_st_less_stat,    key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_SHT_dyn_cmp,            key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_SHB_dyn_cmp_stat,       key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_SHB_st_cmp,             key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_SHT_st_cmp,             key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_SHB_dyn_less,           key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_SHT_st_less,            key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_SHB_st_less_stat,       key_type, value_type ) \

#else
#   define CDSSTRESS_SplitListMap_SHRCU_1( fixture, test_case, key_type, value_type )
#endif


#   define CDSSTRESS_SplitListMap_SHRCU( fixture, test_case, key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHB_dyn_cmp,         key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHT_dyn_cmp_stat,    key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHT_dyn_less,        key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHB_st_less,         key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_SHT_st_less_stat,    key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_SHB_dyn_cmp,            key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_SHT_dyn_cmp_stat,       key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_SHT_dyn_less,           key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_SHB_st_less,            key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_SHT_st_less_stat,       key_type, value_type ) \
        CDSSTRESS_SplitListMap_SHRCU_1( fixture, test_case, key_type, value_type ) \
        CDSSTRESS_SplitListMap_SHRCU_2( fixture, test_case, key_type, value_type ) \

#else
#   define CDSSTRESS_SplitListMap_SHRCU( fixture, test_case, key_type, value_type )
#endif

#if defined(CDS_STRESS_TEST_LEVEL) && CDS_STRESS_TEST_LEVEL > 1
#   define CDSSTRESS_SplitListMap_HP_2( fixture, test_case, key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_HP_dyn_cmp_seqcst,       key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_DHP_dyn_cmp_seqcst,      key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_HP_dyn_cmp_seqcst,          key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_DHP_dyn_cmp_seqcst,         key_type, value_type ) \

#   define CDSSTRESS_SplitListMap_RCU_2( fixture, test_case, key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPI_dyn_cmp_seqcst,  key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPB_dyn_cmp_seqcst,  key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPT_dyn_cmp_seqcst,  key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPI_dyn_cmp_seqcst,     key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPB_dyn_cmp_seqcst,     key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPT_dyn_cmp_seqcst,     key_type, value_type ) \

#   define CDSSTRESS_SplitListMap_2( fixture, test_case, key_type, value_type ) \
        CDSSTRESS_SplitListMap_HP_2( fixture, test_case, key_type, value_type ) \
        CDSSTRESS_SplitListMap_RCU_2( fixture, test_case, key_type, value_type ) \


#else
#   define CDSSTRESS_SplitListMap_HP_2( fixture, test_case, key_type, value_type )
#   define CDSSTRESS_SplitListMap_RCU_2( fixture, test_case, key_type, value_type )
#   define CDSSTRESS_SplitListMap_2( fixture, test_case, key_type, value_type )
#endif

#if defined(CDS_STRESS_TEST_LEVEL) && CDS_STRESS_TEST_LEVEL == 1
#   define CDSSTRESS_SplitListMap_HP_1( fixture, test_case, key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_DHP_dyn_cmp,             key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_DHP_dyn_cmp_swar,        key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_HP_dyn_cmp_stat,         key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_HP_st_cmp,               key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_DHP_dyn_less,            key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_HP_st_less,              key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_DHP_st_less_stat,        key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_DHP_dyn_cmp,                key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_HP_dyn_cmp_stat,            key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_HP_st_cmp,                  key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_DHP_dyn_less,               key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_HP_st_less,                 key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_DHP_st_less_stat,           key_type, value_type ) \

#   define CDSSTRESS_SplitListMap_RCU_1( fixture, test_case, key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPI_dyn_cmp_stat,    key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPT_dyn_cmp,         key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPT_dyn_cmp_stat,    key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPI_st_cmp,          key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPT_st_cmp,          key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPB_dyn_less,        key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPI_st_less,         key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPT_st_less,         key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPB_st_less_stat,    key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPB_dyn_cmp,            key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPI_dyn_cmp_stat,       key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPT_dyn_cmp_stat,       key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPI_st_cmp,             key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPT_st_cmp,             key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPB_dyn_less,           key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPI_st_less,            key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPT_st_less,            key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPB_st_less_stat,       key_type, value_type ) \
        CDSSTRESS_SplitListMap_SHRCU( fixture, test_case, key_type, value_type ) \

#   define CDSSTRESS_SplitListMap_1( fixture, test_case, key_type, value_type ) \
        CDSSTRESS_SplitListMap_HP_1( fixture, test_case, key_type, value_type ) \
        CDSSTRESS_SplitListMap_RCU_1( fixture, test_case, key_type, value_type ) \

#else
#   define CDSSTRESS_SplitListMap_HP_1( fixture, test_case, key_type, value_type )
#   define CDSSTRESS_SplitListMap_RCU_1( fixture, test_case, key_type, value_type )
#   define CDSSTRESS_SplitListMap_1( fixture, test_case, key_type, value_type )
#endif


#define CDSSTRESS_SplitListMap_HP( fixture, test_case, key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_HP_dyn_cmp,              key_type, value_type ) \
    /* CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_HP_dyn_cmp_swar,         key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_DHP_dyn_cmp_stat,        key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_DHP_st_cmp,              key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_HP_dyn_less,             key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_HP_st_less_stat,         key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_DHP_st_less,             key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_HP_dyn_cmp,                 key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_DHP_dyn_cmp_stat,           key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_DHP_st_cmp,                 key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_HP_dyn_less,                key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_DHP_st_less,                key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_HP_st_less_stat,            key_type, value_type ) */ \
    CDSSTRESS_SplitListMap_HP_1( fixture, test_case, key_type, value_type ) \
    CDSSTRESS_SplitListMap_HP_2( fixture, test_case, key_type, value_type ) \ 

#define CDSSTRESS_SplitListMap_RCU( fixture, test_case, key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPI_dyn_cmp,         key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPB_dyn_cmp,         key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPB_dyn_cmp_swar,    key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPB_dyn_cmp_stat,    key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPB_st_cmp,          key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPI_dyn_less,        key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPT_dyn_less,        key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPB_st_less,         key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPI_st_less_stat,    key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_RCU_GPT_st_less_stat,    key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPI_dyn_cmp,            key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPT_dyn_cmp,            key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPB_dyn_cmp_stat,       key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPB_st_cmp,             key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPI_dyn_less,           key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPT_dyn_less,           key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPB_st_less,            key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPI_st_less_stat,       key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_RCU_GPT_st_less_stat,       key_type, value_type ) \
    CDSSTRESS_SplitListMap_RCU_1( fixture, test_case, key_type, value_type ) \
    CDSSTRESS_SplitListMap_RCU_2( fixture, test_case, key_type, value_type ) \

#define CDSSTRESS_SplitListMap( fixture, test_case, key_type, value_type ) \
    CDSSTRESS_SplitListMap_HP( fixture, test_case, key_type, value_type ) \
    /* CDSSTRESS_SplitListMap_RCU( fixture, test_case, key_type, value_type ) \ */

#if defined(CDS_STRESS_TEST_LEVEL) && CDS_STRESS_TEST_LEVEL > 0
#   define CDSSTRESS_SplitListIterableMap_1( fixture, test_case, key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Iterable_DHP_dyn_cmp,             key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Iterable_HP_dyn_cmp_stat,         key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Iterable_HP_st_cmp,               key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Iterable_DHP_dyn_less,            key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Iterable_HP_st_less,              key_type, value_type ) \
        CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Iterable_DHP_st_less_stat,        key_type, value_type ) \

#else
#   define CDSSTRESS_SplitListIterableMap_1( fixture, test_case, key_type, value_type )
#endif


#define CDSSTRESS_SplitListIterableMap( fixture, test_case, key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Iterable_HP_dyn_cmp,              key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Iterable_DHP_dyn_cmp_stat,        key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Iterable_DHP_st_cmp,              key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Iterable_HP_dyn_less,             key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Iterable_DHP_st_less,             key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Iterable_HP_st_less_stat,         key_type, value_type ) \
    CDSSTRESS_SplitListIterableMap_1( fixture, test_case, key_type, value_type ) \


#define CDSSTRESS_SplitListMap_nogc( fixture, test_case, key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_NOGC_dyn_cmp,            key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_NOGC_dyn_cmp_stat,       key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_NOGC_st_cmp,             key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_NOGC_dyn_less,           key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_NOGC_st_less,            key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Michael_NOGC_st_less_stat,       key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_NOGC_dyn_cmp,               key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_NOGC_dyn_cmp_stat,          key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_NOGC_st_cmp,                key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_NOGC_dyn_less,              key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_NOGC_st_less,               key_type, value_type ) \
    CDSSTRESS_SplitListMap_case( fixture, test_case, SplitList_Lazy_NOGC_st_less_stat,          key_type, value_type ) \

#endif // ifndef CDSUNIT_MAP_TYPE_SPLIT_LIST_H
