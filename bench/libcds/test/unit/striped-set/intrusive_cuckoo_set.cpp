// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#include "test_intrusive_set.h"

#include <cds/intrusive/cuckoo_set.h>

namespace {
    namespace ci = cds::intrusive;

    class IntrusiveCuckooSet : public cds_test::intrusive_set
    {
    protected:
        typedef cds_test::intrusive_set base_class;

        typedef base_class::hash_int hash1;


        template <typename Set>
        void test( Set& s, std::vector< typename Set::value_type >& data )
        {
            // Precondition: set is empty
            // Postcondition: set is empty

            base_class::test_< Set::c_isSorted>( s, data );

            size_t const nSetSize = base_class::kSize;

            // clear
            for ( auto& i : data ) {
                i.clear_stat();
                ASSERT_TRUE( s.insert( i ));
            }
            ASSERT_FALSE( s.empty());
            ASSERT_CONTAINER_SIZE( s, nSetSize );

            s.clear();

            ASSERT_TRUE( s.empty());
            ASSERT_CONTAINER_SIZE( s, 0 );
            for ( auto& i : data ) {
                EXPECT_EQ( i.nDisposeCount, 1u );
            }

        }

        //void SetUp()
        //{}

        //void TearDown()
        //{}
    };


//************************************************************
// striped base hook

    TEST_F( IntrusiveCuckooSet, striped_list_basehook_unordered )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 > >  item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_basehook_unordered )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<4>, 0 >> item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef ci::cuckoo::base_hook< ci::cuckoo::probeset_type< item_type::probeset_type >> hook;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s( 32, 4 );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_list_basehook_ordered_cmp )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s( 32, 6, 4 );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_basehook_ordered_cmp )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<8>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::compare< cmp<item_type> >
                , ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( ht );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_list_basehook_ordered_less )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                , ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( 32, 6, 4, ht );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_basehook_ordered_less )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_list_basehook_ordered_cmpmix )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( 32, 6, 0, std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_basehook_ordered_cmpmix )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_list_basehook_ordered_stat )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::stat< ci::cuckoo::stat >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_basehook_ordered_stat )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::stat< ci::cuckoo::stat >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_list_basehook_unordered_storehash )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 2 >> item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef ci::cuckoo::base_hook<
                ci::cuckoo::probeset_type< item_type::probeset_type >
                ,ci::cuckoo::store_hash< item_type::hash_array_size >
            > hook;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
            typedef ci::cuckoo::stat stat;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_basehook_unordered_storehash )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<4>, 2 >> item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef ci::cuckoo::base_hook<
                ci::cuckoo::probeset_type< item_type::probeset_type >
                ,ci::cuckoo::store_hash< item_type::hash_array_size >
            > hook;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
            typedef ci::cuckoo::stat stat;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s( 32, 4 );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_list_basehook_ordered_storehash )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 2 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                    ,ci::cuckoo::store_hash< item_type::hash_array_size >
                > >
                ,cds::opt::hash< std::tuple< hash1, hash2 > >
                ,cds::opt::less< less<item_type> >
                ,cds::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( 32, 6, 0, std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_basehook_ordered_storehash )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 2 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                    ,ci::cuckoo::store_hash< item_type::hash_array_size >
                > >
                ,cds::opt::hash< std::tuple< hash1, hash2 > >
                ,cds::opt::less< less<item_type> >
                ,cds::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( std::move( ht ));
            test( s, data );
        }
    }

//************************************************************
// striped member hook

    TEST_F( IntrusiveCuckooSet, striped_list_memberhook_unordered )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 > >  item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef ci::cuckoo::member_hook< offsetof( item_type, hMember )> hook;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_memberhook_unordered )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<4>, 0 >> item_type;
        struct set_traits: public ci::cuckoo::traits
        {

            typedef ci::cuckoo::member_hook< offsetof( item_type, hMember ), ci::cuckoo::probeset_type< item_type::member_type::probeset_type >> hook;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s( 32, 4 );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_list_memberhook_ordered_cmp )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s( 32, 6, 4 );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_memberhook_ordered_cmp )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<8>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::compare< cmp<item_type> >
                , ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( ht );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_list_memberhook_ordered_less )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                , ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( 32, 6, 4, ht );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_memberhook_ordered_less )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_list_memberhook_ordered_cmpmix )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( 32, 6, 0, std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_memberhook_ordered_cmpmix )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_list_memberhook_ordered_stat )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::stat< ci::cuckoo::stat >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_memberhook_ordered_stat )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::stat< ci::cuckoo::stat >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_list_memberhook_unordered_storehash )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 2 >> item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                ,ci::cuckoo::store_hash< item_type::member_type::hash_array_size >
            > hook;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
            typedef ci::cuckoo::stat stat;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_memberhook_unordered_storehash )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<4>, 2 >> item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                ,ci::cuckoo::store_hash< item_type::member_type::hash_array_size >
            > hook;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
            typedef ci::cuckoo::stat stat;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s( 32, 4 );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_list_memberhook_ordered_storehash )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 2 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                    ,ci::cuckoo::store_hash< item_type::member_type::hash_array_size >
                > >
                ,cds::opt::hash< std::tuple< hash1, hash2 > >
                ,cds::opt::less< less<item_type> >
                ,cds::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( 32, 6, 0, std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, striped_vector_memberhook_ordered_storehash )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 2 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                    ,ci::cuckoo::store_hash< item_type::member_type::hash_array_size >
                > >
                ,cds::opt::hash< std::tuple< hash1, hash2 > >
                ,cds::opt::less< less<item_type> >
                ,cds::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( std::move( ht ));
            test( s, data );
        }
    }

//************************************************************
// refinable base hook

    TEST_F( IntrusiveCuckooSet, refinable_list_basehook_unordered )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 > >  item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef ci::cuckoo::refinable<> mutex_policy;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_basehook_unordered )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<4>, 0 >> item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef ci::cuckoo::refinable<> mutex_policy;
            typedef ci::cuckoo::base_hook< ci::cuckoo::probeset_type< item_type::probeset_type >> hook;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s( 32, 4 );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_list_basehook_ordered_cmp )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s( 32, 6, 4 );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_basehook_ordered_cmp )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<8>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::compare< cmp<item_type> >
                , ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( ht );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_list_basehook_ordered_less )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( 32, 6, 4, ht );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_basehook_ordered_less )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_list_basehook_ordered_cmpmix )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( 32, 6, 0, std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_basehook_ordered_cmpmix )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_list_basehook_ordered_stat )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::stat< ci::cuckoo::stat >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_basehook_ordered_stat )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::stat< ci::cuckoo::stat >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_list_basehook_unordered_storehash )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 2 >> item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef ci::cuckoo::base_hook<
                ci::cuckoo::probeset_type< item_type::probeset_type >
                ,ci::cuckoo::store_hash< item_type::hash_array_size >
            > hook;
            typedef ci::cuckoo::refinable<> mutex_policy;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
            typedef ci::cuckoo::stat stat;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_basehook_unordered_storehash )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<4>, 2 >> item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef ci::cuckoo::base_hook<
                ci::cuckoo::probeset_type< item_type::probeset_type >
                ,ci::cuckoo::store_hash< item_type::hash_array_size >
            > hook;
            typedef ci::cuckoo::refinable<> mutex_policy;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
            typedef ci::cuckoo::stat stat;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s( 32, 4 );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_list_basehook_ordered_storehash )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::list, 2 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                    ,ci::cuckoo::store_hash< item_type::hash_array_size >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,cds::opt::hash< std::tuple< hash1, hash2 > >
                ,cds::opt::less< less<item_type> >
                ,cds::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( 32, 6, 0, std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_basehook_ordered_storehash )
    {
        typedef base_class::base_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 2 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::base_hook<
                    ci::cuckoo::probeset_type< item_type::probeset_type >
                    ,ci::cuckoo::store_hash< item_type::hash_array_size >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,cds::opt::hash< std::tuple< hash1, hash2 > >
                ,cds::opt::less< less<item_type> >
                ,cds::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( std::move( ht ));
            test( s, data );
        }
    }

//************************************************************
// refinable member hook

    TEST_F( IntrusiveCuckooSet, refinable_list_memberhook_unordered )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 > >  item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef ci::cuckoo::member_hook< offsetof( item_type, hMember )> hook;
            typedef ci::cuckoo::refinable<> mutex_policy;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_memberhook_unordered )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<4>, 0 >> item_type;
        struct set_traits: public ci::cuckoo::traits
        {

            typedef ci::cuckoo::member_hook< offsetof( item_type, hMember ), ci::cuckoo::probeset_type< item_type::member_type::probeset_type >> hook;
            typedef ci::cuckoo::refinable<> mutex_policy;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s( 32, 4 );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_list_memberhook_ordered_cmp )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s( 32, 6, 4 );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_memberhook_ordered_cmp )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<8>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( ht );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_list_memberhook_ordered_less )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( 32, 6, 4, ht );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_memberhook_ordered_less )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_list_memberhook_ordered_cmpmix )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( 32, 6, 0, std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_memberhook_ordered_cmpmix )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_list_memberhook_ordered_stat )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::stat< ci::cuckoo::stat >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_memberhook_ordered_stat )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 0 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,ci::opt::hash< std::tuple< hash1, hash2 > >
                ,ci::opt::less< less<item_type> >
                ,ci::opt::compare< cmp<item_type> >
                ,ci::opt::stat< ci::cuckoo::stat >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_list_memberhook_unordered_storehash )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 2 >> item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                ,ci::cuckoo::store_hash< item_type::member_type::hash_array_size >
            > hook;
            typedef ci::cuckoo::refinable<> mutex_policy;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
            typedef ci::cuckoo::stat stat;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s;
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_memberhook_unordered_storehash )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<4>, 2 >> item_type;
        struct set_traits: public ci::cuckoo::traits
        {
            typedef ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                ,ci::cuckoo::store_hash< item_type::member_type::hash_array_size >
            > hook;
            typedef ci::cuckoo::refinable<> mutex_policy;
            typedef cds::opt::hash_tuple< hash1, hash2 > hash;
            typedef base_class::equal_to<item_type> equal_to;
            typedef mock_disposer disposer;
            typedef ci::cuckoo::stat stat;
        };
        typedef ci::CuckooSet< item_type, set_traits > set_type;

        std::vector< typename set_type::value_type > data;
        {
            set_type s( 32, 4 );
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_list_memberhook_ordered_storehash )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::list, 2 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                    ,ci::cuckoo::store_hash< item_type::member_type::hash_array_size >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,cds::opt::hash< std::tuple< hash1, hash2 > >
                ,cds::opt::less< less<item_type> >
                ,cds::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( 32, 6, 0, std::move( ht ));
            test( s, data );
        }
    }

    TEST_F( IntrusiveCuckooSet, refinable_vector_memberhook_ordered_storehash )
    {
        typedef base_class::member_int_item< ci::cuckoo::node< ci::cuckoo::vector<6>, 2 >> item_type;

        typedef ci::CuckooSet< item_type
            ,ci::cuckoo::make_traits<
                ci::opt::hook< ci::cuckoo::member_hook< offsetof( item_type, hMember ),
                    ci::cuckoo::probeset_type< item_type::member_type::probeset_type >
                    ,ci::cuckoo::store_hash< item_type::member_type::hash_array_size >
                > >
                ,ci::opt::mutex_policy<ci::cuckoo::refinable<>>
                ,cds::opt::hash< std::tuple< hash1, hash2 > >
                ,cds::opt::less< less<item_type> >
                ,cds::opt::compare< cmp<item_type> >
                ,ci::opt::disposer< mock_disposer >
            >::type
        > set_type;

        std::vector< typename set_type::value_type > data;
        {
            typename set_type::hash_tuple_type ht;
            set_type s( std::move( ht ));
            test( s, data );
        }
    }

} // namespace
