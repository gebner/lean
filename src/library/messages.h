/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <string>
#include <vector>
#include <util/period.h>
#include "kernel/pos_info_provider.h"
#include "util/output_channel.h"
#include "util/exception.h"

namespace lean {

enum message_severity { INFORMATION, WARNING, ERROR };

class message {
    std::string      m_file_name;
    pos_info         m_pos;
    message_severity m_severity;
    std::string      m_caption, m_text;
public:
    message(std::string const & file_name, pos_info const & pos,
            message_severity severity, std::string const & caption, std::string const & text) :
            m_file_name(file_name), m_pos(pos),
            m_severity(severity), m_caption(caption), m_text(text) {}
    message(std::string const & file_name, pos_info const & pos,
            message_severity severity, std::string const & text) :
            message(file_name, pos, severity, std::string(), text) {}
    message(std::string const & file_name, pos_info const & pos,
            message_severity severity) :
            message(file_name, pos, severity, std::string()) {}
    message(parser_exception const & ex);

    std::string get_file_name() const { return m_file_name; }
    pos_info get_pos() const { return m_pos; }
    message_severity get_severity() const { return m_severity; }
    std::string get_caption() const { return m_caption; }
    std::string get_text() const { return m_text; }
};

struct message_bucket_id {
    name m_bucket;
    period m_version;
};

class message_buffer {
public:
    virtual ~message_buffer() {}
    virtual void start_bucket(message_bucket_id const & bucket);
    virtual void report(message_bucket_id const & bucket, message const & msg);
    virtual void finish_bucket(message_bucket_id const & bucket, std::vector<name> const & children);
};

using null_message_buffer = message_buffer;

class stream_message_buffer : public message_buffer {
    std::shared_ptr<output_channel> m_out;
public:
    stream_message_buffer(std::shared_ptr<output_channel> const & out) : m_out(out) {}
    void report(message_bucket_id const & bucket, message const & msg) override;
};

message_buffer & get_global_message_buffer();
class scoped_message_buffer {
    message_buffer * m_old;
public:
    scoped_message_buffer(message_buffer * msg_buf);
    ~scoped_message_buffer();
};

class scope_message_context {
    scope_message_context * m_old;
    message_bucket_id m_bucket;
    std::vector<name> m_sub_buckets;
public:
    scope_message_context(message_bucket_id const &);
    scope_message_context(message_bucket_id const &, std::vector<name> const & sub_buckets_to_reuse);
    scope_message_context(std::string const &, std::vector<name> const & sub_buckets_to_reuse);
    scope_message_context(std::string const &);
    scope_message_context();
    ~scope_message_context();

    message_bucket_id get_bucket_id() const { return m_bucket; }
    std::vector<name> get_sub_buckets() const { return m_sub_buckets; }

    message_bucket_id new_sub_bucket();
    message_bucket_id new_sub_bucket(std::string const &);
};

message_bucket_id get_global_msg_bucket_id();
scope_message_context & get_scope_message_context();
void report_message(message const &);

}
