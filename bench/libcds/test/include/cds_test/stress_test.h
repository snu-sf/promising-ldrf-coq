// Copyright (c) 2006-2018 Maxim Khizhinsky
//
// Distributed under the Boost Software License, Version 1.0. (See accompanying
// file LICENSE or copy at http://www.boost.org/LICENSE_1_0.txt)

#ifndef CDSTEST_STRESS_TEST_H
#define CDSTEST_STRESS_TEST_H

#include <map>
#include <cds_test/fixture.h>
#include <cds_test/thread.h>

namespace cds_test {

    // Test configuration
    class config
    {
    public:
        std::string get( const char * pszParamName, const char * pszDefVal = NULL ) const
        {
            std::string strParamName( pszParamName );
            auto it = m_Cfg.find( strParamName );
            if ( it == m_Cfg.end())
                return std::string( pszDefVal ); // param not found -> returns default value
            return it->second;
        }

        int get_int( const char * pszParamName, int defVal = 0 ) const
        {
            std::string strParamName( pszParamName );
            cfg_map::const_iterator it = m_Cfg.find( strParamName );
            if ( it == m_Cfg.end())
                return defVal; // param not found -> returns default value
            return atoi( it->second.c_str());
        }

        unsigned int get_uint( const char * pszParamName, unsigned int defVal = 0 ) const
        {
            std::string strParamName( pszParamName );
            cfg_map::const_iterator it = m_Cfg.find( strParamName );
            if ( it == m_Cfg.end())
                return defVal; // param not found -> returns default value
            return static_cast<unsigned int>( strtoul( it->second.c_str(), NULL, 10 ));
        }

        long get_long( const char * pszParamName, long defVal = 0 ) const
        {
            std::string strParamName( pszParamName );
            cfg_map::const_iterator it = m_Cfg.find( strParamName );
            if ( it == m_Cfg.end())
                return defVal; // param not found -> returns default value
            return strtol( it->second.c_str(), NULL, 10 );
        }

        unsigned long get_ulong( const char * pszParamName, unsigned long defVal = 0 ) const
        {
            std::string strParamName( pszParamName );
            cfg_map::const_iterator it = m_Cfg.find( strParamName );
            if ( it == m_Cfg.end())
                return defVal; // param not found -> returns default value
            return strtoul( it->second.c_str(), NULL, 10 );
        }

        size_t get_size_t( const char * pszParamName, size_t defVal = 0 ) const
        {
            std::string strParamName( pszParamName );
            cfg_map::const_iterator it = m_Cfg.find( strParamName );
            if ( it == m_Cfg.end())
                return defVal; // param not found -> returns default value
            return static_cast<size_t>( strtoul( it->second.c_str(), NULL, 10 ));
        }

        bool get_bool( const char * pszParamName, bool defVal = false ) const
        {
            std::string strParamName( pszParamName );
            cfg_map::const_iterator it = m_Cfg.find( strParamName );
            if ( it == m_Cfg.end())
                return defVal; // param not found -> returns default value
            return !( it->second.empty()
                   || it->second == "0"
                   || it->second == "false"
                   || it->second == "no"
                   );
        }

    private:
        typedef std::map< std::string, std::string >  cfg_map;
        cfg_map m_Cfg; // map param_name => value

        friend class config_file;
    };

    class property_stream
    {
    public:
        static std::string const& stat_prefix();
        static void set_stat_prefix( char const* prefix );
    };

    struct stat_prefix
    {
        char const* prefix_;

        stat_prefix()
            : prefix_( nullptr )
        {}

        stat_prefix( char const* prefix )
            : prefix_( prefix )
        {}
    };

    static inline property_stream& operator<<( property_stream& s, stat_prefix&& prefix )
    {
        s.set_stat_prefix( prefix.prefix_ );
        return s;
    }

    template <typename T>
    static inline property_stream& operator <<( property_stream& s, std::pair<char const*, T > prop )
    {
        std::stringstream ss;
        ss << prop.second;
        ::testing::Test::RecordProperty( prop.first, ss.str().c_str());
        return s;
    }

    template <typename T>
    static inline property_stream& operator <<( property_stream& s, std::pair<std::string, T > prop )
    {
        std::stringstream ss;
        ss << prop.second;
        ::testing::Test::RecordProperty( prop.first.c_str(), ss.str().c_str());
        return s;
    }

    static inline property_stream& operator <<( property_stream& s, std::pair<char const*, std::chrono::milliseconds > prop )
    {
        std::stringstream ss;
        ss << prop.second.count();
        ::testing::Test::RecordProperty( prop.first, ss.str().c_str());
        return s;
    }

#define CDSSTRESS_STAT_OUT_( name, val ) std::make_pair( name, val )
#define CDSSTRESS_STAT_OUT( s, field ) CDSSTRESS_STAT_OUT_( property_stream::stat_prefix() + "." #field, s.field.get())

    class stress_fixture : public fixture
    {
        typedef fixture base_class;

    protected:
        stress_fixture()
            : m_thread_pool( *this )
        {}

        //static void SetUpTestCase();
        //static void TearDownTestCase();
        void TearDown()
        {
            print_hp_stat();
            base_class::TearDown();
        }

        thread_pool& get_pool()
        {
            return m_thread_pool;
        }

        static void print_hp_stat();

    public:
        static config const& get_config( char const * slot );
        static config const& get_config( std::string const& slot );

        static std::vector<std::string> load_dictionary();

        static property_stream& propout();

    private:
        thread_pool     m_thread_pool;
    };


    // Internal functions
    void init_config( int argc, char **argv );

} // namespace cds_test

#endif // CDSTEST_FIXTURE_H
