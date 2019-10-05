package org.hisp.dhis.artemis.audit;

/*
 * Copyright (c) 2004-2019, University of Oslo
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * Redistributions of source code must retain the above copyright notice, this
 * list of conditions and the following disclaimer.
 *
 * Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 * Neither the name of the HISP project nor the names of its contributors may
 * be used to endorse or promote products derived from this software without
 * specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
 * ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Map;

import com.google.common.base.Strings;
import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;
import org.hisp.dhis.artemis.MessageManager;
import org.hisp.dhis.artemis.ProducerConfiguration;
import org.hisp.dhis.audit.AuditScope;
import org.hisp.dhis.render.RenderService;
import org.springframework.stereotype.Component;

/**
 * @author Morten Olav Hansen <mortenoh@gmail.com>
 */
@Component
public class AuditManager
{
    private static final Log log = LogFactory.getLog( AuditManager.class );

    private final AuditProducerSupplier auditProducerSupplier;

    private final RenderService renderService;

    private final ProducerConfiguration config;

    private final AuditScheduler auditScheduler;

    public AuditManager( AuditProducerSupplier auditProducerSupplier, RenderService renderService,
        AuditScheduler auditScheduler, ProducerConfiguration config )
    {
        checkNotNull( auditProducerSupplier );
        checkNotNull( renderService );
        checkNotNull( config );

        this.auditProducerSupplier = auditProducerSupplier;
        this.renderService = renderService;
        this.config = config;
        this.auditScheduler = auditScheduler;
    }

    public void send( Audit audit )
    {
        if ( config.isUseQueue() )
        {
            auditScheduler.addAuditItem( audit );
        }
        else
        {
            auditProducerSupplier.publish( audit );
        }

    }


}
